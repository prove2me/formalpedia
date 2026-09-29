-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:25:41.458412+00:00
-- url     : https://prove2.me/submissions/69b6b150-16e2-4f44-be2d-71b48639009a

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
import Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_norm_heatFlow_apply_le
import Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_isCoercive_compress
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (A : E →L[ℂ] E) {mu : ℝ}
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hA : IsCoercive A mu) (x : F)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heatFlow (compress V A) t x‖ ≤ Real.exp (-(mu * t)) * ‖x‖ := norm_heatFlow_apply_le _ (isCoercive_compress V A hVV hA) x ht
