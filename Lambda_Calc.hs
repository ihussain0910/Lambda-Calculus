--------------------------------------------
--                                        --
--     CM20256Functional Programming      --
--                                        --
--         Coursework 2021/2022           --
--                                        --
--------------------------------------------



------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


------------------------- Assignment 1: Simple types

data Type = Base | Type :-> Type
            deriving Eq

nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (   a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)

-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Type Term
  | Apply    Term Term
  deriving Eq

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty


-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" (Base :-> Base) (Lambda "x"  Base (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))



sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f"))
    )))

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x t n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z t n)
    | z == x    = Lambda z t n
    | otherwise = Lambda z t (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y t m)
    | x == y    = Lambda y t m
    | otherwise = Lambda z t (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)


beta :: Term -> [Term]
beta (Apply (Lambda x t n) m) =
  [substitute x m n] ++
  [Apply (Lambda x t n') m  | n' <- beta n] ++
  [Apply (Lambda x t n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x t n) = [Lambda x t n' | n' <- beta n]
beta (Variable _) = []


-- - - - - - - - - - - -- Normalize


normalize :: Term -> IO ()
normalize m = do
  putStrLn (show (bound m) ++ " -- " ++ show m)
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)



------------------------- Assignment 2: Type checking


type Context = [(Var, Type)]


extend :: (Var, Type) -> Context -> Context
extend x con = x : con

find :: Eq a => a -> [(a,b)] -> b
find _ [] = error "A variable in the term is not found in the context"
find a ((x,y):xs)
      | a == x = y
      | otherwise = find a xs



typeof :: Context -> Term -> Type

typeof c (Variable x) = find x c

typeof c (Lambda x t n) = t :-> typeof (extend (x,t) c) n

typeof c (Apply x y) =
                      case typeof c x of
                        Base -> error "Expecting ARROW type, but given BASE type"
                        ty :-> ty' | ty == typeof c y -> ty'
                        _ :-> _ :-> _ -> error "Incorrect type given"
                        _ :-> _ -> error "Incorrect type given" 

example8 = Lambda "x" Base (Apply (Apply (Variable "f") (Variable "x")) (Variable "x"))



------------------------- Assignment 3: Functionals

data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f


-- - - - - - - - - - - -- Examples

{--fplussix :: Functional -> Functiona
fplussix (Num x) = do 
                    let y = x+6
                    Num y
fplussix (Fun f) = error "fun f "--}


plussix :: Functional
plussix = Fun fplussix
    where
        fplussix (Num x) = Num (x+6)
        fplussix (Fun f) = error "fun f "


-- plus : N -> (N -> N)
plus :: Functional
plus = Fun fplus1
       where
            fplus1 (Num i) = Fun (fplus2 i)
                     where
                       fplus2 x (Num j) = Num (x + j)
                       fplus2 x (Fun _) = error "Error"
            fplus1 (Fun f) = error "Error"

twicetst :: (Functional -> Functional) -> Functional -> Functional
twicetst func (Num i) = func (func (Num i))
twicetst func (Fun _) = error "error"



twice :: Functional
twice = Fun twice1
        where
            twice1 f = Fun (twice2 f)
                     where twice2 f (Num i) = fun f (fun f (Num i))
                           twice2 f (Fun _) = error "Error"


--twice f x = f (f x)

-- - - - - - - - - - - -- Constructing functionals

dummy :: Type -> Functional
dummy Base = Num 0
dummy (o :-> t) = Fun f
                      where f x = dummy t


count :: Type -> Functional -> Int
count Base (Num i)= i
count (o :-> t) (Fun f) = count t (f (dummy o))

increment :: Functional -> Int -> Functional
increment (Num x) i = Num (x + i)
increment (Fun f) i = Fun g
                          where g x = increment (f x) i


------------------------- Assignment 4 : Counting reduction steps

type Valuation = [(Var, Functional)]

findV :: Eq a => a -> [(a,b)] -> b
findV _ [] = error "A variable in the term is not found in the context"
findV a ((x,y):xs)
      | a == x = y
      | otherwise = findV a xs

extendV :: (Var, Functional) -> Valuation -> Valuation
extendV x val = x : val

interpret :: Context -> Valuation -> Term -> Functional
interpret c v (Variable x) = findV x v
interpret c val (Lambda x t2 m) =  Fun f
                                   where f g = interpret (extend (x,t2) c) (extendV (x,g) val) m
interpret c val (Apply x y) = increment (fun f g) (1 + count (typeof c y) g)
                              where
                                f = interpret c val x
                                g = interpret c val y


bound :: Term -> Int
bound m = count (typeof [] m) (interpret [] [] m )
