-- Prove2me | solution 1 for ErlerGross.gamma_multiplication_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T19:52:08.228977+00:00
-- url     : https://prove2.me/submissions/275be99a-5667-4958-af48-39a6e18161b2

import Mathlib
import Theorems.Thm_ErlerGross_digamma_multiplication_formula
import Theorems.Thm_ErlerGross_gamma_multiplication_formula_of_digamma

theorem solution (n : Nat) (hn : 0 < n) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  exact ErlerGross.gamma_multiplication_formula_of_digamma n hn
    (fun z hz => ErlerGross.digamma_multiplication_formula n hn z hz)