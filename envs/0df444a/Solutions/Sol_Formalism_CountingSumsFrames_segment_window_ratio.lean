-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_window_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:10.410611+00:00
-- url     : https://prove2.me/submissions/bca61175-81ea-4c3f-bc47-d7ffc54950b5

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_window_dim_ratio_le_exp
import Theorems.Thm_Formalism_CountingSumsFrames_window_numeric_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegWindowRatio := by
  intro p N N₁ r Y a b' Q La P C C' h hP hPQ hC hC' hCh hCh'
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  have hY0 : 0 < Y := by linarith
  have hK0 : 0 < (r : ℝ) + 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hP0 : 0 < P := by linarith
  have hW : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y)) ≤ 1 * a := by
    rw [mul_div_cancel₀ _ (by positivity)]; linarith
  have h3 : 3 * (((r : ℝ) + 1) ^ 2 * P * Y) ≤ a := le_trans (by gcongr) hK2QY
  have h9 : 9 * (((r : ℝ) + 1) * P) ≤ a := le_trans (by gcongr) hKQ
  obtain ⟨hlo, hnum⟩ := window_numeric_bound (R := r) (w := 1) hK hY hP0 (by positivity) hW (by norm_num)
    (by norm_num) h3 h9
  have e : ((1 : ℝ) + 1) / Y = 2 / Y := by norm_num
  rw [e] at hnum
  exact window_dim_ratio_le_exp r C C' _ _ (2 / Y) hlo (by positivity) hnum hC hC' hCh hCh'
end Formalism.CountingSumsFrames
