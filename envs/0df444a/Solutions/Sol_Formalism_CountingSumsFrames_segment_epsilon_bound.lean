-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_epsilon_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:00.995059+00:00
-- url     : https://prove2.me/submissions/25e7cffe-8f6e-41b6-926f-b4cfdfda59ae

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_segment_log_bound
import Theorems.Thm_Formalism_CountingSumsFrames_segment_sum_ratio_le
import Theorems.Thm_Formalism_CountingSumsFrames_forty_eight_le_kappa

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
theorem _root_.solution : SegEps := by
  intro p N N₁ r s Y a b' Q La P S Y' h hP hS0 hS hY'
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ x : ℝ, x = Real.log a := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ x : ℝ, x = kapSeg p a r s := ⟨_, rfl⟩
  rw [← hk] at hp h2 hl6 hY'
  rw [← hlg] at hl2 hl4 hl6 ⊢
  rw [← hLd] at h2 hL1 hl5
  rw [← hκd] at hκ ⊢
  unfold SbdSeg at hS
  have hk3 : 3 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hlgL : lg ≤ 4 * L := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hu := segment_sum_ratio_le hk0 hY0 hL0 ha0 hb0 hp h2 hP hS0 hS hY'
  have hY'0 : 0 < Y' := lt_of_lt_of_le (by positivity) hY'
  obtain ⟨u, hud⟩ : ∃ x : ℝ, x = S / Y' := ⟨_, rfl⟩
  rw [← hud] at hu
  have hu0 : 0 ≤ u := by rw [hud]; positivity
  have hY3 : Y ≤ Y^3 := le_self_pow₀ hY (by norm_num)
  have hk21 : 1 ≤ k^2 := one_le_pow₀ (by linarith)
  have hk31 : 1 ≤ k^3 := one_le_pow₀ (by linarith)
  have hYk3 : Y ≤ k^3*Y^3 := by
    calc Y = 1 * Y := by ring
      _ ≤ k^3*Y^3 := mul_le_mul hk31 hY3 hY0.le (by positivity)
  have hYk2 : Y ≤ k^2*Y^3 := by
    calc Y = 1 * Y := by ring
      _ ≤ k^2*Y^3 := mul_le_mul hk21 hY3 hY0.le (by positivity)
  have hYL : Y ≤ Y * L := le_mul_of_one_le_right hY0.le hL1
  have hα : 8/(k^3*Y^3) ≤ 8/Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYk3
  have hβ : 4/(Y*L) ≤ 4/Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYL
  have e12 : 8/Y + 4/Y = 12/Y := by ring
  have c1 : u ≤ 12 / Y := by linarith
  have hα2 : 8/(k^3*Y^3) * lg ≤ 32 / Y := by
    calc 8/(k^3*Y^3) * lg ≤ 8/(k^3*Y^3) * (4*k) := mul_le_mul_of_nonneg_left hl6 (by positivity)
      _ = 32/(k^2*Y^3) := by field_simp; ring
      _ ≤ 32 / Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYk2
  have hβ2 : 4/(Y*L) * lg ≤ 16 / Y := by
    calc 4/(Y*L) * lg ≤ 4/(Y*L) * (4*L) := mul_le_mul_of_nonneg_left hlgL (by positivity)
      _ = 16 / Y := by field_simp; ring
  have e48 : 32/Y + 16/Y = 48/Y := by ring
  have c2 : u * lg ≤ 48 / Y := by
    have := mul_le_mul_of_nonneg_right hu hlg0
    rw [add_mul] at this
    linarith
  have eS : S * lg / Y' = u * lg := by rw [hud]; ring
  refine ⟨by rw [← hud]; exact c1, by rw [eS]; exact c2, hκ, ?_⟩
  unfold epsSeg
  have e1 : 2 * S / Y' = 2 * u := by rw [hud]; ring
  have e2 : 2 * S * lg / Y' = 2 * (u * lg) := by rw [hud]; ring
  rw [e1, e2]
  have h48 : 48 / Y ≤ 48 := div_le_self (by norm_num) hY
  have hκ0 : 0 < κ := by linarith
  have c3 : (2 * κ + 2 * (u * lg)) / (Y * κ) ≤ 4 / Y := by
    calc (2 * κ + 2 * (u * lg)) / (Y * κ) ≤ (4 * κ) / (Y * κ) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 4 / Y := by field_simp
  have e28 : 2 * (12 / Y) + 4 / Y = 28 / Y := by ring
  linarith
end Formalism.CountingSumsFrames
