-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_short_window_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.447311+00:00
-- url     : https://prove2.me/submissions/9be9f024-b250-4838-884e-d246fbe85edd

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegShortWindowNoTie := by
  intro p k Y a b' P hY hk hp hb0 h2 hL haP
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < Real.log a := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have ha0 : 0 < a := by
    by_contra hneg
    have hneg := not_lt.1 hneg
    have h1 : a / b' ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hb0.le
    have h3 : 0 < (k:ℝ)*Y^2*Real.log a := by positivity
    linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (k:ℝ) * Y := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := by
    rw [hw]
    calc (2:ℝ) = 2 * 1 := by norm_num
      _ ≤ (k:ℝ) * Y := by gcongr
  have hw0 : 0 < w := by linarith
  rw [← hw] at haP
  have hP0 : 0 < P := lt_trans (div_pos ha0 hw0) haP
  have hpw : w^2 ≤ (p:ℝ) := by rw [hw, mul_pow]; exact hp
  have hp2 : 8 * w ≤ (p:ℝ)^2 := by
    have h8 : (8:ℝ) ≤ w^3 := by
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ w^3 := by gcongr
    calc 8 * w ≤ w^3 * w := by gcongr
      _ = (w^2)^2 := by ring
      _ ≤ (p:ℝ)^2 := by gcongr
  have hp20 : 0 < (p:ℝ)^2 := by linarith
  have hA : 4 * a / (p:ℝ)^2 ≤ a / (2*w) := by
    rw [div_le_div_iff₀ hp20 (by positivity)]
    have := mul_le_mul_of_nonneg_left hp2 ha0.le
    linarith
  have hB : 2 * b' < a / (2*w) := by
    rw [lt_div_iff₀ (by positivity)]
    have h3 := (le_div_iff₀ hb0).1 h2
    have h4 : (k:ℝ) * Y * b' ≤ (k:ℝ) * Y^2 * b' := by
      have : Y ≤ Y^2 := le_self_pow₀ hY (by norm_num)
      gcongr
    have h5 : (k:ℝ) * Y^2 * b' * 4 < (k:ℝ) * Y^2 * b' * Real.log a :=
      mul_lt_mul_of_pos_left hL (by positivity)
    rw [hw]
    nlinarith
  have hsum : a / (2*w) + a / (2*w) = a / w := by field_simp; ring
  rw [Int.floor_eq_zero_iff]; unfold SbdSeg
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hP0]
  linarith
end Formalism.CountingSumsFrames
