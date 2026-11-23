-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_epsilon_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:24.092283+00:00
-- url     : https://prove2.me/submissions/5ee1186d-fc06-4ab0-90b9-5fd0719beb63

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_segment_log_bound
import Theorems.Thm_Formalism_CountingSumsFrames_segment_ratio_le
import Theorems.Thm_Formalism_CountingSumsFrames_forty_eight_le_kappa
import Theorems.Thm_Formalism_CountingSumsFrames_first_depth_bounds

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
theorem _root_.solution : SegEpsPlus := by
  intro p N N₁ r s t Y a b' Q La J Yp h hts hJ0 hJ hYp
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨hD1, hD2⟩ := first_depth_bounds (t := t) hY (by linarith : 0 ≤ kapSeg p a r s)
  have hx0 : initialExponent p a r s t + lgSeg p a r ≤ kapSeg p a r s - 1 := by
    unfold initialExponent kapSeg
    obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
    rw [← hlg] at hl2 ⊢
    have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
    have htr : (t:ℝ) ≤ s := by exact_mod_cast hts
    have h1 : (t:ℝ)*((r:ℝ)+1) ≤ (s:ℝ)*((r:ℝ)+1) := mul_le_mul_of_nonneg_right htr (by linarith)
    have h2' : 2*(r:ℝ) ≤ (r:ℝ)^2 := by nlinarith
    have h3 : ((s:ℝ)+2)*(2*(r:ℝ)) ≤ ((s:ℝ)+2)*(r:ℝ)^2 := mul_le_mul_of_nonneg_left h2' (by linarith)
    have h4' : 0 ≤ (s:ℝ)*(r:ℝ) := by positivity
    have hc : 1 ≤ 3*((s:ℝ)+2)*(r:ℝ)^2 - ((r:ℝ) + (t:ℝ)*((r:ℝ)+1) + (2*(s:ℝ)+2)*((r:ℝ)-1) + 1) := by
      nlinarith
    have hm : (1:ℝ) * 1 ≤ (3*((s:ℝ)+2)*(r:ℝ)^2 - ((r:ℝ) + (t:ℝ)*((r:ℝ)+1) + (2*(s:ℝ)+2)*((r:ℝ)-1) + 1)) * lg :=
      mul_le_mul hc (by linarith) zero_le_one (by linarith)
    linarith
  have hceil : ((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) + lgSeg p a r ≤ kapSeg p a r s := by
    have := Int.ceil_lt_add_one (initialExponent p a r s t)
    linarith
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = ((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ x : ℝ, x = Real.log a := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ x : ℝ, x = kapSeg p a r s := ⟨_, rfl⟩
  rw [← hk] at hp h2 hl6 hYp
  rw [← hX] at hceil ⊢
  rw [← hlg] at hl2 hl4 hl6 hx0 hceil ⊢
  rw [← hLd] at h2 hL1 hl5 ⊢
  rw [← hκd] at hκ hD1 hD2 hx0 hceil ⊢
  obtain ⟨D, hDd⟩ : ∃ x : ℝ, x = firstDepth t Y κ := ⟨_, rfl⟩
  rw [← hDd] at hD1 hD2 ⊢
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hlgL : lg ≤ 4 * L := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hw : 0 < a / (k * Y) := by positivity
  have hv : J / Yp ≤ 3/2 * (1 / (Y * L)) := by
    calc J / Yp ≤ J / (a / (k*Y)) := div_le_div_of_nonneg_left hJ0 hw hYp
      _ ≤ (3 * b' / 2) / (a / (k*Y)) := div_le_div_of_nonneg_right hJ hw.le
      _ = 3/2 * (k * Y * b' / a) := by field_simp
      _ ≤ 3/2 * (1 / (Y * L)) := mul_le_mul_of_nonneg_left (segment_ratio_le hk0 hY0 hL0 ha0 hb0 h2) (by norm_num)
  have hYL0 : 0 < 1 / (Y * L) := by positivity
  have c2 : J / Yp ≤ 2 / (Y * L) := by
    have : 2 / (Y * L) = 2 * (1 / (Y * L)) := by ring
    rw [this]; linarith
  have c3 : J * lg / Yp ≤ 8 / Y := by
    have e : J * lg / Yp = J / Yp * lg := by ring
    rw [e]
    calc J / Yp * lg ≤ 3/2 * (1 / (Y * L)) * lg := mul_le_mul_of_nonneg_right hv hlg0
      _ ≤ 3/2 * (1 / (Y * L)) * (4 * L) := mul_le_mul_of_nonneg_left hlgL (by positivity)
      _ = 6 / Y := by field_simp; ring
      _ ≤ 8 / Y := div_le_div_of_nonneg_right (by norm_num) hY0.le
  refine ⟨hD1, c2, c3, hx0, hceil, ?_⟩
  unfold epsPlusSeg
  have hD0 : 0 < D := by linarith
  have hE : Y * D < ((⌊Y * D⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hYD : 0 < Y * D := by positivity
  have h8 : 8 / Y ≤ 8 := div_le_self (by norm_num) hY
  have c4 : (X + D + lg + J * lg / Yp) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1) ≤ 3 / Y := by
    calc (X + D + lg + J * lg / Yp) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1)
        ≤ (3 * D) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1) := div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ (3 * D) / (Y * D) := div_le_div_of_nonneg_left (by linarith) hYD hE.le
      _ = 3 / Y := by field_simp
  have c5 : 2 / (Y * L) ≤ 2 / Y :=
    div_le_div_of_nonneg_left (by norm_num) hY0 (le_mul_of_one_le_right hY0.le hL1)
  have e5 : 2 / Y + 3 / Y = 5 / Y := by ring
  linarith
end Formalism.CountingSumsFrames
