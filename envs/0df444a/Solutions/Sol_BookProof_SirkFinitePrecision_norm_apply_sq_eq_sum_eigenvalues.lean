-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:54:03.596941+00:00
-- url     : https://prove2.me/submissions/1539ab4e-ea28-4566-ac4b-08ca977b3280

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_repr_apply_of_symmetric
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖T x‖ ^ 2 = ∑ i, hT.eigenvalues hn i ^ 2 * ‖coeff hT hn x i‖ ^ 2 := by

  rw [norm_sq_eq_sum_repr hT hn (T x)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [repr_apply_of_symmetric hT hn x i, norm_mul]
  simp [mul_pow, sq_abs]
