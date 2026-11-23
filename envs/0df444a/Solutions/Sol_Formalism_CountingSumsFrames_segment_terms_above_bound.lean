-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_terms_above_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.484444+00:00
-- url     : https://prove2.me/submissions/11cf2617-2331-4435-940b-a0e73c90f87e

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds

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
theorem _root_.solution : SegTermsAboveS := by
  intro p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have ha0 : 0 < a := by linarith
  have hk2 : (9:ℝ) ≤ ((r:ℝ)+1)^2 := by
    calc (9:ℝ) = 3 ^ 2 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hkQ0 : 0 ≤ ((r:ℝ)+1) * Q := by positivity
  have hkQ : 9 * (((r:ℝ)+1) * Q) ≤ b' := by
    calc 9 * (((r:ℝ)+1) * Q) = 9 * (((r:ℝ)+1) * Q) * 1 := by ring
      _ ≤ ((r:ℝ)+1)^2 * (((r:ℝ)+1) * Q) * Y := by gcongr
      _ = ((r:ℝ)+1)^3 * Q * Y := by ring
      _ ≤ b' := h4
  have hp81 : (81:ℝ) ≤ (p:ℝ)^2 := by
    calc (81:ℝ) = 9 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have h81 : 4/(p:ℝ)^2 ≤ 4/81 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp81
  have ha9 : 9 * b' < a := by
    have : 9 * b' ≤ (p:ℝ) * b' := mul_le_mul_of_nonneg_right hp9 hb0.le
    linarith
  have hz : a * (4/(p:ℝ)^2) ≤ a * (4/81) := mul_le_mul_of_nonneg_left h81 ha0.le
  have hfirst : 4 * b' + ((r : ℝ) + 1) * Q ≤ a * (1 - 4 / (p : ℝ) ^ 2) := by
    have : a * (1 - 4 / (p : ℝ) ^ 2) = a - a * (4/(p:ℝ)^2) := by ring
    rw [this]; linarith
  refine ⟨hfirst, ?_⟩
  intro P C A j hP1 hPQ hC hA hj
  have hP0 : 0 < P := by linarith
  have hfl : ((⌊SbdSeg p a b' P⌋ : ℤ) : ℝ) ≤ SbdSeg p a b' P := Int.floor_le _
  have hCP : a - ((r:ℝ)+1) * P ≤ C * P := by
    have := mul_le_mul_of_nonneg_right hC hP0.le
    have e : (a / P - ((r:ℝ)+1)) * P = a - ((r:ℝ)+1) * P := by
      rw [sub_mul, div_mul_cancel₀ _ hP0.ne']
    linarith
  have hAP : (A:ℝ) * P ≤ 3 * b' / 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * P)).1 hA
    linarith
  have hjA : (j:ℝ) * P ≤ A * P := by
    have : (j:ℝ) ≤ A := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_right this hP0.le
  have hkP : ((r:ℝ)+1) * P ≤ ((r:ℝ)+1) * Q := mul_le_mul_of_nonneg_left hPQ (by linarith)
  have hS : SbdSeg p a b' P ≤ (C:ℝ) - j := by
    unfold SbdSeg
    rw [div_le_iff₀ hP0]
    have e1 : a * (1 - 4 / (p : ℝ) ^ 2) = a - 4 * a / (p:ℝ)^2 := by ring
    rw [e1] at hfirst
    have e2 : ((C:ℝ) - j) * P = C * P - j * P := by ring
    rw [e2]; linarith
  have : ((⌊SbdSeg p a b' P⌋ : ℤ) : ℝ) ≤ (((C:ℤ) - (j:ℤ) : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this
end Formalism.CountingSumsFrames
