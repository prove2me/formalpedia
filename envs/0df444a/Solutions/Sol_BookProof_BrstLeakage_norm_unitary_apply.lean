-- Prove2me | solution 1 for BookProof.BrstLeakage.norm_unitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:25.879633+00:00
-- url     : https://prove2.me/submissions/7009e6aa-b55f-4fc9-87b1-da74494e4cc9

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.norm_unitary_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (x : E) :
    ‖U x‖ = ‖x‖ := by

  have h : star U * U = 1 := hU.1
  have hx : (ContinuousLinearMap.adjoint U) (U x) = x := by
    have : ((star U * U) : E →L[ℂ] E) x = (1 : E →L[ℂ] E) x := by rw [h]
    simpa [ContinuousLinearMap.star_eq_adjoint] using this
  have h2 : (inner ℂ (U x) (U x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hx]
  have h3 : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    have := congrArg Complex.re h2
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using this
  nlinarith [norm_nonneg (U x), norm_nonneg x, h3]
