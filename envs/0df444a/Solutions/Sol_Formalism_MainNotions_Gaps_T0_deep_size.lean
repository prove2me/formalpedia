-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.deep_size
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:03.918262+00:00
-- url     : https://prove2.me/submissions/92a0556a-be20-46c8-b7f6-fe47b6f0f98b

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
theorem _root_.solution {T D ΛW Λ0 lrw A E G Prw tableDegreeThreeBase PE L F0 κ : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T) (hG : 0 ≤ G)
    (hPrw : 0 ≤ Prw) (hPE : 0 ≤ PE) (hF0 : 0 ≤ F0) (hκ : 1 ≤ κ) (hTκ : T ≤ κ)
    (hW : ΛW ≤ G * L) (h0 : Λ0 ≤ G * F0) (hrw : lrw ≤ Prw * (L - 1))
    (hn : (T - D) * L + F0 = κ + T - D) (hA : A ≤ tableDegreeThreeBase * κ) (hE : E ≤ PE) :
    (T - D) * (ΛW + lrw) + Λ0 + A + E ≤ (2 * G + Prw + tableDegreeThreeBase + PE) * κ := by
  have hTD : 0 ≤ T - D := by linarith
  have e1 : (T - D) * ΛW ≤ (T - D) * (G * L) := mul_le_mul_of_nonneg_left hW hTD
  have e2 : (T - D) * lrw ≤ (T - D) * (Prw * (L - 1)) := mul_le_mul_of_nonneg_left hrw hTD
  have e3 : G * (κ + T - D) ≤ G * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) hG
  have e4 : G * ((T - D) * L + F0) = G * (κ + T - D) := by rw [hn]
  have e5 : Prw * ((T - D) * L + F0) = Prw * (κ + T - D) := by rw [hn]
  have e6 : 0 ≤ Prw * F0 := mul_nonneg hPrw hF0
  have e7 : PE ≤ PE * κ := le_mul_of_one_le_right hPE hκ
  linarith
end Formalism.MainNotions.Gaps.T0
