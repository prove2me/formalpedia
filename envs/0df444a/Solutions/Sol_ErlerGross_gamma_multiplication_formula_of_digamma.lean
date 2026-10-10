-- Prove2me | solution 1 for ErlerGross.gamma_multiplication_formula_of_digamma
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:32:18.055814+00:00
-- url     : https://prove2.me/submissions/f4e6a10f-c968-423b-a8a2-6d5e163c3720

import Mathlib
import Theorems.Thm_ErlerGross_gamma_product_right_half_plane_of_digamma
import Theorems.Thm_ErlerGross_gamma_product_extend_from_right_half_plane

theorem solution (n : Nat) (hn : 0 < n)
    (hpsi : forall z : Complex, 0 < z.re ->
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
        n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex)) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  obtain ⟨c, hc, hpos⟩ :=
    ErlerGross.gamma_product_right_half_plane_of_digamma n hn hpsi
  exact ⟨c, hc, ErlerGross.gamma_product_extend_from_right_half_plane n hn c hc hpos⟩
