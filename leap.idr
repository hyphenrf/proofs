{-
  We'd like to prove that:
    isLeapYear year =
      (mod year 4 == 0) && ((mod year 400 == 0) || not (mod year 100 == 0))

  is equivalent to:
    isLeapYear year = mod year 4 == 0 && mod year 100 /= 0 || mod year 400 == 0

  by proving that the only case where they're not equivalent (when the year is
  divisible by 400 but not by 4) is impossible. In other words, proving that if
  a year is divisible by 400 then it's divisible by 4.
-}


-- Props ----------------------------------------------------------------------

leap : (year : Integer) ->
  let p = mod year 4   == 0
      q = mod year 100 == 0
      r = mod year 400 == 0
      v = mod year 100 /= 0
   in
      p && (r || not q) = p && v || r

pqr : {p, q, r : Bool} -> r && not p = False -> p && (r || q) = p && q || r

-- Can't do much with Integer and mod ...
axiom : {n : Integer} -> mod n 400 == 0 && not (mod n 4 == 0) = False

-- ... So let's prove an "equivalent" theorem that uses more friendly encodings
equiv : {n : Nat} -> (k ** n = 400 * k) -> (k ** n = 4 * k)


-- Proofs ---------------------------------------------------------------------

leap y = pqr axiom

equiv (k ** h) = (100 * k ** rewrite h in masoc {n = 4} {m = 100})
  where
    mdist : {n, m : Nat}    -> (n + m) * k = (n * k) + (m * k)
    masoc : {n, m : Nat}    -> (n * m) * k = n * (m * k)
    pasoc : {n, m, k : Nat} -> (n + m) + k = n + (m + k)

    pasoc {n = 0}   = Refl
    pasoc {n = S n} = cong S pasoc

    masoc {n = 0}   = Refl
    masoc {n = S n} = rewrite mdist {n = m, m = n * m} in
                      rewrite masoc {n, m} in Refl

    mdist {n = 0}   = Refl
    mdist {n = S n} = rewrite pasoc {n = k, m = n * k, k = m * k} in
                      rewrite mdist {n, m} in Refl


noth : {a : Bool} -> not a = False -> a = True
andh : {a, b : Bool} -> a && b = False -> Either (b = False) (a = False)
orcom : {a, b : Bool} -> a || b = b || a

pqr hyp with (andh hyp)
 _| Right hr = rewrite hr in orcom
 _| Left hnp = rewrite noth {a = p} $ hnp in orcom

noth {a = False} _ impossible
noth {a = True}  _ = Refl

andh {a = False} _ = Right Refl
andh {b = False} _ = Left  Refl

orcom {a = False, b = False} = Refl
orcom {a = False, b = True}  = Refl
orcom {a = True,  b = False} = Refl
orcom {a = True,  b = True}  = Refl

