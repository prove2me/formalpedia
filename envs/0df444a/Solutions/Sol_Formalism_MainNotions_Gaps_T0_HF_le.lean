-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.HF_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:26.811308+00:00
-- url     : https://prove2.me/submissions/4b735b7f-e4d1-4e0f-8170-222d86950be2

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
theorem _root_.solution {HL HF δ D G PH PI4 Prw L aG2 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG2 ≤ 4 / 3 * (D + 4) * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * w) :
    HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L := by
  have e1 : aG2 * w ≤ 4 / 3 * (D + 4) * δ * (Prw * L) :=
    (mul_le_mul_of_nonneg_right ha hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have e2 := mul_le_mul_of_nonneg_left e1 hD
  have e3 : D * aG2 * w = D * (aG2 * w) := by ring
  have e4 : (D + 4) * HL ≤ (D + 4) * ((D + 1) * δ * (2 * G + 4 * PH) * L) :=
    mul_le_mul_of_nonneg_left hHL (by positivity)
  have q0 : 0 ≤ δ * L * (D + 4) * (D + 1) * (PH - PI4 - Prw) := mul_nonneg (by positivity) (by linarith)
  have q1 : 0 ≤ δ * L * PI4 * D ^ 2 := by positivity
  have q2 : 0 ≤ δ * L * PI4 * D := by positivity
  have q3 : 0 ≤ δ * L * PI4 := by positivity
  have q4 : 0 ≤ δ * L * Prw * D ^ 2 := by positivity
  have q5 : 0 ≤ δ * L * Prw * D := by positivity
  have q6 : 0 ≤ δ * L * Prw := by positivity
  linarith
end Formalism.MainNotions.Gaps.T0
