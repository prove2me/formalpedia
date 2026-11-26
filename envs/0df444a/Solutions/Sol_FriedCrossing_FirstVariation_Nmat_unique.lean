-- Prove2me | solution 1 for FriedCrossing.FirstVariation.Nmat_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:59:10.402962+00:00
-- url     : https://prove2.me/submissions/e40fc39f-3d90-44da-a0ef-34e00cd9ae02

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_FirstVariation_det_Bmat
import Theorems.Thm_FriedCrossing_FirstVariation_Bmat_mul_Nmat

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (N : Matrix (Fin 2) (Fin 2) K) (hN : Bmat Bcc Bcψ Bψc Bψψ * N = Pmat p) :
    N = Nmat Bcc Bcψ Bψc Bψψ p := by
  have h1 : Bmat Bcc Bcψ Bψc Bψψ * (N - Nmat Bcc Bcψ Bψc Bψψ p) = 0 := by
    rw [Matrix.mul_sub, hN, Bmat_mul_Nmat h, sub_self]
  have h2 : (Bmat Bcc Bcψ Bψc Bψψ).adjugate * (Bmat Bcc Bcψ Bψc Bψψ *
      (N - Nmat Bcc Bcψ Bψc Bψψ p)) = 0 := by rw [h1, Matrix.mul_zero]
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, det_Bmat] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 h
  · exact sub_eq_zero.mp h3
end FriedCrossing.FirstVariation
