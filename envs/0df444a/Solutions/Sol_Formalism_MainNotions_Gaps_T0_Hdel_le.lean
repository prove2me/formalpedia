-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.Hdel_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:35.15059+00:00
-- url     : https://prove2.me/submissions/fba7d61e-37dc-4a59-aeb3-96b9f0a2d61b

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution {HL Hδ δ D G PH PI4 Prw L aG1 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG1 ≤ 4 / 3 * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : Hδ ≤ HL + (δ * PI4 * D * L + D * aG1 * w)) :
    Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L := by
  have e1 : aG1 * w ≤ 4 / 3 * δ * (Prw * L) :=
    (mul_le_mul_of_nonneg_right ha hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have e2 := mul_le_mul_of_nonneg_left e1 hD
  have e3 : D * aG1 * w = D * (aG1 * w) := by ring
  have q1 : 0 ≤ δ * D * L * (PH - PI4 - Prw) := mul_nonneg (by positivity) (by linarith)
  have q2 : 0 ≤ δ * D * L * PI4 := by positivity
  have q3 : 0 ≤ δ * D * L * Prw := by positivity
  have q4 : 0 ≤ δ * L * PH := mul_nonneg (by positivity) (by linarith)
  linarith
end Formalism.MainNotions.Gaps.T0
