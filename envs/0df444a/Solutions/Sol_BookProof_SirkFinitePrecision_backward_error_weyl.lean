-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.backward_error_weyl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:25:21.402618+00:00
-- url     : https://prove2.me/submissions/cb47fb5d-9ba6-4846-a0d5-c8d8ab528cc4

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.backward_error_weyl
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_exists_eigenvalue_dist_le_residual
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {ε : ℝ} (hε : ∀ x : E, ‖T x - S x‖ ≤ ε * ‖x‖)
    {lam : ℝ} (hlam : HasRealEigenvalue S lam) :
    ∃ mu : ℝ, HasRealEigenvalue T mu ∧ |mu - lam| ≤ ε := by

  obtain ⟨x, hx0, hx⟩ := hlam
  obtain ⟨mu, hmu, hle⟩ := exists_eigenvalue_dist_le_residual hT hn hx0 lam
  refine ⟨mu, hmu, ?_⟩
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hres : ‖T x - (lam : ℂ) • x‖ ≤ ε * ‖x‖ := by
    have hxx : T x - (lam : ℂ) • x = T x - S x := by rw [hx]
    rw [hxx]; exact hε x
  exact le_of_mul_le_mul_right (by linarith [hle.trans hres]) hnx
