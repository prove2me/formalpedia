-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_initial_kappa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:24.744229+00:00
-- url     : https://prove2.me/submissions/90a60b47-7f75-4c2c-9f11-e6e550f14959

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_log_bounds_of_nine_le

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
theorem _root_.solution : SegKap0 := by
  intro p N N₁ r s Y a b' Q La ap h hs hap1 hap2
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  have hk0 : kap0I p N (r + 1) a = 2 * N * (((r : ℝ) + 1) * Real.logb p a) := by
    unfold kap0I; push_cast; ring
  rw [hk0]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have ha0 : 0 < a := by linarith
  have hKY : 0 < ((r : ℝ) + 1) * Y := by positivity
  have hx : 0 < 2 / (((r : ℝ) + 1) * Y) := by positivity
  have e1 : Real.log ap ≤ Real.log a + 2 / (((r : ℝ) + 1) * Y) := by
    calc Real.log ap ≤ Real.log (a * (1 + 2 / (((r : ℝ) + 1) * Y))) :=
          Real.log_le_log (by linarith) hap2
      _ = Real.log a + Real.log (1 + 2 / (((r : ℝ) + 1) * Y)) :=
          Real.log_mul ha0.ne' (by positivity)
      _ ≤ Real.log a + 2 / (((r : ℝ) + 1) * Y) := by
          have := Real.log_le_sub_one_of_pos (x := 1 + 2 / (((r : ℝ) + 1) * Y)) (by positivity)
          linarith
  have e2 : (r : ℝ) * (2 / (((r : ℝ) + 1) * Y)) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hKY]
    nlinarith
  have e3 : (r : ℝ) * Real.log ap ≤ ((r : ℝ) + 1) * Real.log a := by
    have : (r : ℝ) * Real.log ap ≤ (r : ℝ) * (Real.log a + 2 / (((r : ℝ) + 1) * Y)) := by gcongr
    linarith
  have e4 : (r : ℝ) * Real.logb p ap ≤ ((r : ℝ) + 1) * Real.logb p a := by
    unfold Real.logb
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right e3 (by linarith)
  have e5 : 0 ≤ (r : ℝ) * Real.logb p ap :=
    mul_nonneg hr0 (Real.logb_nonneg (by linarith) (by linarith))
  have hs' : (s : ℝ) + 1 ≤ N := by exact_mod_cast hs
  calc (2 * (s : ℝ) + 2) * (r : ℝ) * Real.logb p ap
      = (2 * (s : ℝ) + 2) * ((r : ℝ) * Real.logb p ap) := by ring
    _ ≤ 2 * N * (((r : ℝ) + 1) * Real.logb p a) :=
        mul_le_mul (by linarith) e4 e5 (by positivity)
end Formalism.CountingSumsFrames
