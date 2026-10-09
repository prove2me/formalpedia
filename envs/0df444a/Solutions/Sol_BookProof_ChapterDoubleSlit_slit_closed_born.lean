-- Prove2me | solution 1 for BookProof.ChapterDoubleSlit.slit_closed_born
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:04.842192+00:00
-- url     : https://prove2.me/submissions/cbe7f95a-6f6c-49ef-b509-46ee9deab96f

-- Generated from ChapterDoubleSlit.lean — solution of BookProof.ChapterDoubleSlit.slit_closed_born
import Mathlib
import Definitions.Def_ChapterDoubleSlit
import Theorems.Thm_BookProof_ChapterDoubleSlit_Hpsi0
open BookProof.ChapterDoubleSlit



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin 2) : bornProb (H *ᵥ psi0) i = 1 / 2 := by

  rw [Hpsi0]
  simp only [bornProb]
  rw [show (1 / Real.sqrt 2 : ℂ) = ((Real.sqrt 2 : ℝ):ℂ)⁻¹ by rw [one_div]]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num
