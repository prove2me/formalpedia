-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_top_room
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:55.873797+00:00
-- url     : https://prove2.me/submissions/7901cef0-7d80-452d-8eea-334596342227

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds

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
theorem _root_.solution : SegSTopRoom := by
  intro p N N₁ r Y a b' Q La P Qj A0 sg C h hP hPQ hpP hA0 hsg hC
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have h9P : 9 * P ≤ Qj := le_trans (by gcongr) hpP
  have hQj : 0 < Qj := by linarith
  have haP : 0 < a / P := by positivity
  have h1 : a / Qj ≤ a / P / 9 := by
    rw [div_div, mul_comm P 9]
    gcongr
  have h2' : La * A0 ≤ K * (a / P / 9) := by
    calc La * A0 ≤ La * (a / P / 9) := by gcongr; linarith
      _ ≤ K * (a / P / 9) := by gcongr
  have h3 : sg ≤ 2 / 9 * (a / P) := by
    calc sg ≤ 2 * La * A0 / K := hsg
      _ = 2 * (La * A0) / K := by ring
      _ ≤ 2 * (K * (a / P / 9)) / K := by gcongr
      _ = 2 / 9 * (a / P) := by field_simp
  have h4' : K ≤ 1 / 9 * (a / P) := by
    have h9 : 9 * (K * P) ≤ a := le_trans (by gcongr) hKQ
    rw [← mul_div_assoc, le_div_iff₀ hP]
    linarith
  exact ⟨h3, by linarith, by linarith⟩
end Formalism.CountingSumsFrames
