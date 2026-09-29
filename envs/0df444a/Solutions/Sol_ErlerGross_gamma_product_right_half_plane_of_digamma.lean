-- Prove2me | solution 1 for ErlerGross.gamma_product_right_half_plane_of_digamma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:39:51.832297+00:00
-- url     : https://prove2.me/submissions/45235bba-3b3d-4ae7-86b3-8e43feb9c49d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ErlerGross_gamma_multiplication_formula_of_digamma

theorem solution (n : Nat) (hn : 0 < n)
    (hpsi : forall z : Complex, 0 < z.re ->
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
        n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex)) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex, 0 < z.re ->
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  obtain ⟨c, hc, hmul⟩ :=
    ErlerGross.gamma_multiplication_formula_of_digamma n hn hpsi
  exact ⟨c, hc, fun z _ => hmul z⟩
