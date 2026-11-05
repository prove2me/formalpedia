-- Prove2me | solution 1 for BookProof.ChapterAttentionResponse.norm_headOutput_sub_le_temperature
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T20:04:54.146971+00:00
-- url     : https://prove2.me/submissions/e16e51e8-9d24-4832-a602-271dfa4603d4

-- Generated from ChapterAttentionResponse.lean — solution of BookProof.ChapterAttentionResponse.norm_headOutput_sub_le_temperature
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Theorems.Thm_BookProof_ChapterAttentionResponse_hasDerivAt_headOutput
import Theorems.Thm_BookProof_ChapterAttentionResponse_norm_scoreValueCovariance_le
import Theorems.Thm_BookProof_ChapterAttentionResponse_abs_score_sub_meanScore_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionResponse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in

theorem solution {s : Fin m → ℝ} {v : Fin m → E} {C a b : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (ha : ∀ l, a ≤ s l) (hb : ∀ l, s l ≤ b) (i : Fin m)
    (beta gamma : ℝ) :
    ‖headOutput gamma s v - headOutput beta s v‖ ≤ C * (b - a) * |gamma - beta| := by
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun t : ℝ => headOutput t s v) (scoreValueCovariance x s v)
        Set.univ x := fun x _ => (hasDerivAt_headOutput x s v).hasDerivWithinAt
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖scoreValueCovariance x s v‖ ≤ C * (b - a) :=
    fun x _ => norm_scoreValueCovariance_le x hv (abs_score_sub_meanScore_le ha hb x) i
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.mem_univ beta) (Set.mem_univ gamma)
  simpa [Real.norm_eq_abs] using this
