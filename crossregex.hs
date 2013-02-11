{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Data.Char (digitToInt)
import qualified Data.Foldable as Fold
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Set as S
import System.Environment
import Text.InterpolatedString.Perl6
import qualified Text.Parsec as P
import qualified Text.PrettyPrint.HughesPJ as PP

main :: IO ()
main = do
  [file] <- getArgs
  print =<< solve =<< hexFromFile file

--
-- Character set
--

data C
  = Char {-# UNPACK #-} !Char
  | Alien
  deriving (Show, Eq, Ord)

data CSet
  = Only !(S.Set C)
  | Except !(S.Set C)

instance Show CSet where
  show = PP.render . pprCSet

universe :: CSet
universe = Except S.empty

isEmpty :: CSet -> Bool
isEmpty (Only a) = S.null a
isEmpty _ = False

complement :: CSet -> CSet
complement (Only a) = Except a
complement (Except a) = Only a

intersection :: CSet -> CSet -> CSet
intersection (Only a) (Only b) = Only (S.intersection a b)
intersection (Only a) (Except b) = Only (S.difference a b)
intersection (Except a) (Only b) = Only (S.difference b a)
intersection (Except a) (Except b) = Except (S.union a b)

consistent :: CSet -> CSet -> Bool
consistent x y = not $ isEmpty $ intersection x y

singleton :: C -> CSet
singleton = Only . S.singleton

isSingleton :: CSet -> Bool
isSingleton (Only a) = S.size a == 1
isSingleton Except{} = False

member :: C -> CSet -> Bool
member x (Only b) = S.member x b
member x (Except b) = S.notMember x b

delete :: C -> CSet -> CSet
delete x y = intersection y (complement $ singleton x)

mentionedInCs :: CSet -> S.Set C
mentionedInCs (Only s) = s
mentionedInCs (Except s) = s

--
-- Regular expressions
--

data Regex
  = Append Regex Regex
  | AnyOf CSet
  | Closure Regex
  | Choose Regex Regex
  | Capture !Int Regex Regex -- let <n> = <captured> in <next>
  | Ref !Int -- reference <n>
  | Eps

instance Show Regex where
  show = PP.render . pprRegex

hasBackref :: Regex -> Bool
hasBackref re = case re of
  Append a b -> hasBackref a || hasBackref b
  AnyOf{} -> False
  Closure x -> hasBackref x
  Choose a b -> hasBackref a || hasBackref b
  Capture _ a b -> hasBackref a || hasBackref b
  Ref{} -> True
  Eps -> False

mentionedSet :: Regex -> S.Set C
mentionedSet re = case re of
  Append a b -> S.union (mentionedSet a) (mentionedSet b)
  AnyOf cs -> mentionedInCs cs
  Closure x -> mentionedSet x
  Choose a b -> S.union (mentionedSet a) (mentionedSet b)
  Capture _ a b -> S.union (mentionedSet a) (mentionedSet b)
  Ref{} -> S.empty
  Eps -> S.empty

--
-- Backtracking matcher
--

btMatch :: Regex -> [CSet] -> Bool
btMatch regex xs = not $ null $ runStateT bt st
  where
    st = BTState{ btInput = xs, btCaptured = IM.empty }
    bt = do
      _ <- btMatches regex
      [] <- gets btInput
      return ()

type BT = StateT BTState []

data BTState = BTState
  { btInput :: ![CSet]
  , btCaptured :: !(IntMap [CSet])
  }

btNext :: BT CSet
btNext = do
  bts <- get
  case btInput bts of
    [] -> mzero
    c:cs -> do
      put $! bts{ btInput = cs }
      return c

expect :: CSet -> BT CSet
expect cs = do
  c <- btNext
  guard $ consistent c cs
  return c

capture :: Int -> [CSet] -> BT ()
capture n cap = modify $ \bt -> bt{ btCaptured = IM.insert n cap $ btCaptured bt }

btMatches :: Regex -> BT [CSet]
btMatches regex = case regex of
  Append a b -> (++) <$> btMatches a <*> btMatches b
  AnyOf cs -> (:[]) <$> expect cs
  Closure a -> loop []
    where
      loop xs = return (concat $ reverse xs) `mplus` do
        m@(_:_) <- btMatches a
        loop (m:xs)
  Choose a b -> btMatches a `mplus` btMatches b
  Capture n inner body -> do
    cap <- btMatches inner
    capture n cap
    (cap++) <$> btMatches body
  Ref n -> do
    m <- gets $ IM.lookup n . btCaptured
    case m of
      Nothing -> mzero
      Just u -> mapM expect u
  Eps -> return []

--
-- Problem
--

type Location = Int

data Problem = Problem
  { pPoints :: IntMap ()
  , pConstrs :: [(Regex, [Location])]
  }
  deriving (Show)

-- 0,0 - a,0 (a+1 items)
-- a,0 - a+b,b (b+1 items)
-- a+b,b - a+b,b+c (c+1 items)
-- a+b,b+c - a+b-d,b+c (d+1 items)
-- a+b-d,b+c - a+b-d-e,b+c-e (e+1 items)
-- a+b-d-e,b+c-e - a+b-d-e, b+c-e-f (f+1 items)
hexProblem :: [Regex] -> Int -> Int -> Int -> Int -> Int -> Problem
hexProblem rs a b c d e = Problem{..}
  where
    f = length rs - a - b - c - d - e - 3
    x_max = a+b
    y_max = b+c

    pPoints = IM.fromList $ do
      x <- [0..x_max]
      y <- [0..y_max]
      guard $ valid x y
      return (encode (x, y), ())

    pConstrs = zip rs $ do
      (start_x, start_y, dir_x, dir_y, shift_x, shift_y, len) <-
        [ (0, 0, 0, 1, 1, 0, a)
        , (a, 0, 0, 1, 1, 1, b+1)
        , (a+b, b, -1, -1, 0, 1, c)
        , (a+b, b+c, -1, -1, -1, 0, d+1)
        , (a+b-d, b+c, 1, 0, -1, -1, e)
        , (a+b-d-e, b+c-e, 1, 0, 0, -1, f+1)
        ]
      step <- [0..len-1]
      let !begin_x = start_x + step * shift_x
      let !begin_y = start_y + step * shift_y
      let point n = (begin_x + n * dir_x, begin_y + n * dir_y)
      return $ map encode $ takeWhile (uncurry valid) $ map point [0..]

    encode (x, y) = y * x_max + x

    valid x y =
      0 <= y &&
      x - y <= a &&
      x <= x_max &&
      y <= y_max &&
      y - x <= f &&
      0 <= x

--
-- Solver
--

type SolverEnv = IntMap [Constr]
  -- List of constraints that affect each point

data Constr = Constr
  { cRegex :: !Regex
  , cInput :: [Location]
  , cHasBackref :: !Bool
  , cMentioned :: S.Set C
  }
  deriving Show

makeEnv :: Problem -> SolverEnv
makeEnv Problem{..} = IM.fromListWith (++) $ do
  (cRegex, cInput) <- pConstrs
  let
    constr = Constr
      { cHasBackref = hasBackref cRegex
      , cMentioned = mentionedSet cRegex
      , ..
      }
  pt <- cInput
  return (pt, [constr])

type SolverState = IntMap CSet

type Solver = StateT SolverState (ReaderT SolverEnv IO)

solve :: Problem -> IO Bool
solve pr = runSolver pr $ solverLoop 0

runSolver :: Problem -> Solver a -> IO a
runSolver pr@Problem{..} sol =
  runReaderT (evalStateT sol initialState) $ makeEnv pr
  where
    initialState = universe <$ pPoints

solverLoop :: Int -> Solver Bool
solverLoop n = do
  liftIO $ putStrLn [qq|solver: iteration $n|]
  m <- get
  liftIO $ print m
  done <- gets $ Fold.all isSingleton
  if done
    then return True
    else do
      anyProgress <- solverIter
      if anyProgress
        then solverLoop (n+1)
        else return False

solverIter :: Solver Bool
solverIter = do
  env <- ask
  points <- gets IM.toList
  fmap or $ forM points $ \(point, cs) ->
    if isSingleton cs
      then return False
      else case IM.lookup point env of
        Nothing -> error "foo"
        Just constrs -> reduce point cs constrs

reduce :: Int -> CSet -> [Constr] -> Solver Bool
reduce point cs constrs = do
  m <- get
  let choices = toTest m
  doneAnything <- fmap or $ mapM test (S.toList choices)
  when doneAnything $ do
    modify $ IM.adjust (refine choices) point
    --m1 <- get
    --liftIO $ putStrLn [qq|refined: $point -> {IM.lookup point m1}|]
  return doneAnything
  where
    refine choices cs'
      | member Alien cs' = cs'
      | otherwise = intersection (Only choices) cs'
    test c = foldr (testWith c) (return False) constrs
    testWith c Constr{..} next = do
      m <- get
      let str = map (peek c m) cInput
      --liftIO $ putStrLn [qq|matching $cRegex with $str -> {btMatch cRegex str}|]
      if btMatch cRegex str
        then next
        else do
          --liftIO $ putStrLn [qq|candidate $point: {IM.lookup point m} -> {delete c <$> IM.lookup point m}|]
          put $! IM.adjust (delete c) point m
          return True

    peek c m i
      | i == point = singleton c
      | otherwise = IM.findWithDefault (error "bar") i m

    toTest m = case intersection cs (Only $ specials m) of
      Only s -> s
      _ -> error "quux"
    specials m = S.insert Alien $ S.unions $ do
      Constr{..} <- constrs
      let
        mentionedInRow = S.unions $
          map (mentionedInCs . peek Alien m) cInput
      if cHasBackref
        then return $ S.union cMentioned mentionedInRow
        else return cMentioned

--
-- IO
--

hexFromFile :: FilePath -> IO Problem
hexFromFile path = do
  fmtLine:regexes <- lines <$> readFile path
  let [a, b, c, d, e] = map read $ words fmtLine
  return $ hexProblem (map parseCompleteRegex' regexes)
    a b c d e

--
-- Pretty-printer
--

pprCSet :: CSet -> PP.Doc
pprCSet (Only cs)
  | Just (c, cs') <- S.minView cs
  , S.null cs' = pprC c
pprCSet (Except cs)
  | S.null cs = PP.char '.'
pprCSet u = PP.brackets $ x u
  where
    x (Only cs) = only cs
    x (Except cs) = PP.char '^' PP.<> only cs

    only = PP.cat . map pprC . S.toList

pprC :: C -> PP.Doc
pprC Alien = PP.char '#'
pprC (Char c) = PP.char c

pprRegex :: Regex -> PP.Doc
pprRegex = pprRegexWithParen 0

-- precedence:
--   1 | 0
--   3 <append> 2
--   4 *
pprRegexWithParen :: Int -> Regex -> PP.Doc
pprRegexWithParen prec regex = case regex of
  Append a b -> paren 2 $ PP.fcat [rec 3 a, rec 2 b]
  AnyOf cs -> pprCSet cs
  Closure a -> paren 4 $ rec 4 a PP.<> PP.char '*'
  Choose a b -> paren 0 $ PP.fcat [rec 1 a, PP.char '|', rec 0 b]
  Capture n a b -> paren 2 $ PP.fcat
    [PP.parens $ PP.braces (PP.int n) PP.<> (rec 0 a), rec 2 b]
  Ref k -> PP.char '\\' PP.<> PP.text (show k)
  Eps -> PP.empty
  where
    paren n
      | n < prec = PP.parens
      | otherwise = id
    rec = pprRegexWithParen

--
-- Parser
--

parseCompleteRegex' :: String -> Regex
parseCompleteRegex' str = either error id $ parseCompleteRegex str

parseCompleteRegex :: String -> Either String Regex
parseCompleteRegex str = case P.runP parser () "regex" str of
  Left e -> Left $ show e
  Right v -> Right v
  where
    parser = parseRegex (Just 1) <* P.eof

type Parser = P.Parsec String ()

parseRegex :: Maybe Int -> Parser Regex
parseRegex toplevel = foldr1 Choose <$> (parseSeq toplevel `P.sepBy1` P.char '|')

parseSeq :: Maybe Int -> Parser Regex
parseSeq toplevel = do
  (r0, parened) <- parsePostfix
  capt parened r0 <|> append r0 <|> pure r0
  where
    capt parened r0 = case toplevel of
      Just n
        | parened -> Capture n r0 <$> parseSeq (Just (n+1))
      _ -> fail ""
    append r0 = Append r0 <$> parseSeq toplevel

parsePostfix :: Parser (Regex, Bool)
parsePostfix = do
  (r0, parened) <- simpleRegex
  ((,False) <$> (star r0 <|> plus r0 <|> question r0)) <|> pure (r0, parened)
  where
    star r0 = Closure r0 <$ P.char '*'
    plus r0 = Append r0 (Closure r0) <$ P.char '+'
    question r0 = Choose Eps r0 <$ P.char '?'

simpleRegex :: Parser (Regex, Bool)
simpleRegex = ((,True) <$> parened) <|> ((,False) <$> (anyof <|> ref <|> dot <|> ch))
  where
    anyof = P.char '[' *> (AnyOf <$> parseCSet) <* P.char ']'
    ch = AnyOf . singleton . Char <$> P.noneOf "|)"
    ref = P.char '\\' *> ((Ref . digitToInt) <$> P.digit)
    dot = AnyOf universe <$ P.char '.'
    parened = P.char '(' *> parseRegex Nothing <* P.char ')'

parseCSet :: Parser CSet
parseCSet = constr <*> many (P.noneOf "]")
  where
    constr = Except . set <$ P.char '^'
      <|> pure (Only . set)

    set = S.fromList . map Char

--
-- Test
--

testProblem :: Problem
testProblem = hexProblem rs 1 1 1 1 1
  where
    rs = map parseCompleteRegex'
      [ "[CR][CH]"
      , "[^A]*"
      , "H."
      , "(.)\\1"
      , ".*"
      , ".*H.*"
      , "AU|BT"
      , ".*X.*."
      , "[^R]*"
      ]

literal :: String -> [CSet]
literal = map $ f
  where
    f '.' = universe
    f c = singleton $ Char c

_notUsed :: ()
_notUsed = ()
  where
    _ = testProblem
    _ = literal
