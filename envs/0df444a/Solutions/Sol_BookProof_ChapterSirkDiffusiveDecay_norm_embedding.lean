-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.norm_embedding
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:18:04.348976+00:00
-- url     : https://prove2.me/submissions/a337d536-357a-42a7-908e-f62112bd5d97

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.norm_embedding
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (x : F) : ‖V x‖ = ‖x‖ := by

  have h := congrArg (fun T : F →L[ℂ] F => T x) hVV
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq] at h
  have hin : (inner ℂ (V x) (V x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_left, h]
  have := congrArg Complex.re hin
  simp only [inner_self_eq_norm_sq_to_K] at this
  have hsq : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [← Complex.ofReal_pow] using this
  calc ‖V x‖ = Real.sqrt (‖V x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
