-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.218513+00:00
-- url     : https://prove2.me/submissions/fb215aeb-2cee-4db7-a090-0b5ebe866438

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_clog_le_logb_add_one

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
theorem _root_.solution : SegSize := by
  intro p N N₁ r Y a b' Q La ap P h hap hP
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hS : SbdSeg p a b' P ≤ 3 * a := by
    unfold SbdSeg
    rw [div_le_iff₀ (by linarith)]
    have h81 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have : 4 * a / (p : ℝ) ^ 2 ≤ a := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro n hn
  have hp9' : 9 ≤ p := by exact_mod_cast hp9
  exact clog_le_logb_add_one p n (8 * a + r) (by omega) (by linarith) hn
end Formalism.CountingSumsFrames
