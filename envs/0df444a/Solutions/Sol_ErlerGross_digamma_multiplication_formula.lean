-- Prove2me | solution 1 for ErlerGross.digamma_multiplication_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:28:50.84966+00:00
-- url     : https://prove2.me/submissions/8bcd3705-bd88-422e-96b3-f3b299a0623a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ErlerGross_gamma_multiplication_formula
import Theorems.Thm_ErlerGross_digamma_from_gamma_multiplication

theorem solution (n : Nat) (hn : 0 < n) (z : Complex) (hz : 0 < z.re) :
    Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
  obtain ⟨c, hc, hmul⟩ := ErlerGross.gamma_multiplication_formula n hn
  exact ErlerGross.digamma_from_gamma_multiplication n hn z hz c hc hmul