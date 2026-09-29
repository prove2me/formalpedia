-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:26:42.393694+00:00
-- url     : https://prove2.me/submissions/9aff8d37-3a51-4100-a8c4-7881bdc081d7

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit
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
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) (θ : ℝ) :
    ∃ lam : ℝ, HasRealEigenvalue T lam ∧ |lam - θ| ≤ ‖T x - (θ : ℂ) • x‖ := by

  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hx; simp at hx
  obtain ⟨lam, hlam, hle⟩ := exists_eigenvalue_dist_le_residual hT hn hx0 θ
  exact ⟨lam, hlam, by simpa [hx] using hle⟩
