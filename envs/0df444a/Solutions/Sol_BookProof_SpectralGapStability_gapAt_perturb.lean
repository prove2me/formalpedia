-- Prove2me | solution 1 for BookProof.SpectralGapStability.gapAt_perturb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:20.170048+00:00
-- url     : https://prove2.me/submissions/1ded295e-dbf7-4aca-b675-7532373a9504

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.gapAt_perturb
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A B : F →L[ℂ] F} {lam d eps : ℝ}
    (h : GapAt A lam d) (hAB : ‖A - B‖ ≤ eps) : GapAt B lam (d - eps) := by

  intro x
  have h1 : ‖A x - B x‖ ≤ eps * ‖x‖ := by
    have := (A - B).le_opNorm x
    have hle : ‖A - B‖ * ‖x‖ ≤ eps * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hAB (norm_nonneg x)
    simpa [ContinuousLinearMap.sub_apply] using this.trans hle
  have h2 : ‖A x - (lam : ℂ) • x‖ ≤ ‖B x - (lam : ℂ) • x‖ + ‖A x - B x‖ := by
    have : A x - (lam : ℂ) • x = (B x - (lam : ℂ) • x) + (A x - B x) := by abel
    rw [this]
    exact norm_add_le _ _
  have h3 := h x
  have : (d - eps) * ‖x‖ = d * ‖x‖ - eps * ‖x‖ := by ring
  rw [this]
  linarith
