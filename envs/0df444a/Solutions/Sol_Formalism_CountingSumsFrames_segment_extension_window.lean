-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_extension_window
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:11.07523+00:00
-- url     : https://prove2.me/submissions/98c34752-b58b-4d3f-aa24-c980716064f5

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_log_bounds_of_nine_le
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
theorem _root_.solution : SegExtWindow := by
  intro p N N₁ r Y a b' Q La x h h2' hx0 hx
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  have hY0 : 0 < Y := by linarith
  have hK0 : 0 < (r : ℝ) + 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hl0 : 0 < Real.log a := by linarith
  have hKY0 : 0 < ((r : ℝ) + 1) * Y := by positivity
  have hKY3 : 3 ≤ ((r : ℝ) + 1) * Y := by
    calc (3 : ℝ) = 3 * 1 := by norm_num
      _ ≤ ((r : ℝ) + 1) * Y := by gcongr
  have hU0 : 0 < a / (((r : ℝ) + 1) * Y) := by positivity
  have e0 : ((r : ℝ) + 1) * Y ^ 2 * La * Real.log a * b' ≤ a := (le_div_iff₀ hb0).mp h2'
  have e1 : La * b' ≤ a / (((r : ℝ) + 1) * Y ^ 2 * Real.log a) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have c1 : x ≤ 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) := by
    calc x ≤ 2 * (La * b' / ((r : ℝ) + 1)) := hx
      _ ≤ 2 * (a / (((r : ℝ) + 1) * Y ^ 2 * Real.log a) / ((r : ℝ) + 1)) := by gcongr
      _ = 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) := by field_simp
  have c2' : 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) ≤ 2 / 3 * (a / (((r : ℝ) + 1) * Y)) := by
    rw [div_le_iff₀ (by positivity)]
    have g : 2 / 3 * (a / (((r : ℝ) + 1) * Y)) * (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) =
        2 / 3 * a * (((r : ℝ) + 1) * Y * Real.log a) := by field_simp
    rw [g]
    have g3 : 3 ≤ ((r : ℝ) + 1) * Y * Real.log a := by
      calc (3 : ℝ) = 3 * 1 := by norm_num
        _ ≤ ((r : ℝ) + 1) * Y * Real.log a := by gcongr; linarith
    have g4 : 2 / 3 * a * 3 ≤ 2 / 3 * a * (((r : ℝ) + 1) * Y * Real.log a) := by gcongr
    linarith
  have c2'' : x ≤ 2 / 3 * (a / (((r : ℝ) + 1) * Y)) := c1.trans c2'
  have c2 : x ≤ a / (((r : ℝ) + 1) * Y) := by linarith
  have eU : a * (1 + 2 / (((r : ℝ) + 1) * Y)) = a + 2 * (a / (((r : ℝ) + 1) * Y)) := by ring
  have hU3 : a / (((r : ℝ) + 1) * Y) ≤ a / 3 := by gcongr
  have c5 : 1 / Y + ((r : ℝ) + 1) * x / a ≤ 1 / (3 * Y / 5) := by
    have g1 : ((r : ℝ) + 1) * x / a ≤ ((r : ℝ) + 1) * (2 / 3 * (a / (((r : ℝ) + 1) * Y))) / a := by
      gcongr
    have g2 : ((r : ℝ) + 1) * (2 / 3 * (a / (((r : ℝ) + 1) * Y))) / a = 2 / 3 * (1 / Y) := by
      field_simp
    have g3 : 1 / (3 * Y / 5) = 5 / 3 * (1 / Y) := by field_simp
    rw [g3]
    linarith
  refine ⟨c1, c2, by rw [eU]; linarith, by rw [eU]; linarith, c5, ?_⟩
  intro P C C' hP hPQ hC hC' hCh hCh'
  have hP0 : 0 < P := by linarith
  have hW : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + x) ≤ 2 * a := by
    have g1 : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + x) ≤
        ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + a / (((r : ℝ) + 1) * Y)) := by gcongr
    have g2 : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + a / (((r : ℝ) + 1) * Y)) = 2 * a := by
      field_simp; ring
    linarith
  have h3 : 3 * (((r : ℝ) + 1) ^ 2 * P * Y) ≤ a := le_trans (by gcongr) hK2QY
  have h9 : 9 * (((r : ℝ) + 1) * P) ≤ a := le_trans (by gcongr) hKQ
  obtain ⟨hlo, hnum⟩ := window_numeric_bound (R := r) (w := 2) hK hY hP0 (by positivity) hW (by norm_num)
    (by norm_num) h3 h9
  have e : ((2 : ℝ) + 1) / Y = 3 / Y := by norm_num
  rw [e, ← add_assoc] at hnum
  exact window_dim_ratio_le_exp r C C' _ _ (3 / Y) hlo (by positivity) hnum hC hC' hCh hCh'
end Formalism.CountingSumsFrames
