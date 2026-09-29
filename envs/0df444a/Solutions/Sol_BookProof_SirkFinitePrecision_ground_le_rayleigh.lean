-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.ground_le_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:18:06.581418+00:00
-- url     : https://prove2.me/submissions/b7777b79-28e3-4f8c-945e-874c1faec0f7

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.ground_le_rayleigh
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
import Theorems.Thm_BookProof_SirkFinitePrecision_rayleigh_eq_sum_eigenvalues
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 : ℝ}
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i) :
    lam0 ≤ rayleigh T x := by

  classical
  have hpar : (1 : ℝ) = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by
    rw [← norm_sq_eq_sum_repr hT hn x, hx]; norm_num
  rw [rayleigh_eq_sum_eigenvalues hT hn x]
  calc lam0 = ∑ i, lam0 * ‖coeff hT hn x i‖ ^ 2 := by
        rw [← Finset.mul_sum, ← hpar, mul_one]
    _ ≤ ∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hlow i) (by positivity)
