-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:10.145805+00:00
-- url     : https://prove2.me/submissions/934ae398-b514-4eb1-8c3b-2d2d1bf8bd07

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
theorem _root_.solution {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r:ℝ)+1)^2 * Y^2 ≤ p ∧ ((r:ℝ)+1) * Y^2 * Real.log a ≤ a / b' ∧ Real.log a ≤ (r:ℝ)+1 ∧
    ((r:ℝ)+1)^3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p:ℝ) < a / b' ∧ (2:ℝ) ≤ r ∧ 1 ≤ Q ∧ 0 < b' ∧ (9:ℝ) ≤ p ∧
    27 ≤ b' ∧ (p:ℝ) * b' < a ∧ 1 ≤ Real.log a ∧ (1:ℝ) ≤ N₁ ∧ (r:ℝ) + 1 ≤ b' := by
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hk, hN', hN1', hQ, hb0⟩ := h
  push_cast at hp h2 hlog h4
  have hr : (2:ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
  have hk2 : (9:ℝ) ≤ ((r:ℝ)+1)^2 := by
    calc (9:ℝ) = 3 ^ 2 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hk3 : (27:ℝ) ≤ ((r:ℝ)+1)^3 := by
    calc (27:ℝ) = 3 ^ 3 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hpr : (9:ℝ) ≤ p := by
    calc (9:ℝ) = 9 * 1 := by norm_num
      _ ≤ ((r:ℝ)+1) ^ 2 * Y ^ 2 := by gcongr
      _ ≤ p := hp
  have hb27 : 27 ≤ b' := by
    calc (27:ℝ) = 27 * 1 * 1 := by norm_num
      _ ≤ ((r:ℝ)+1) ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hkb : (r:ℝ) + 1 ≤ b' := by
    have h1 : (r:ℝ) + 1 ≤ ((r:ℝ)+1)^3 := le_self_pow₀ (by linarith) (by norm_num)
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) * 1 * 1 := by ring
      _ ≤ ((r:ℝ)+1) ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hpb : (p:ℝ) * b' < a := (lt_div_iff₀ hb0).mp h6
  have ha : 243 < a := by
    have : (9:ℝ) * 27 ≤ (p:ℝ) * b' := mul_le_mul hpr hb27 (by norm_num) (by linarith)
    linarith
  have hlog1 : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hN1r : (1:ℝ) ≤ N₁ := by exact_mod_cast hN1'
  exact ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hpr, hb27, hpb, hlog1, hN1r, hkb⟩
end Formalism.CountingSumsFrames
