-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:27.235173+00:00
-- url     : https://prove2.me/submissions/6c9ecc91-ba83-46a1-b107-f65f40d56912

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_segment_log_bound
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
theorem _root_.solution : SegDepth := by
  intro p N N₁ r s t Y a b' Q La h hts hsN
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨hD1, hD2⟩ := first_depth_bounds (t := t) hY (by linarith : 0 ≤ kapSeg p a r s)
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have htr : (t:ℝ) ≤ s := by exact_mod_cast hts
  have hsr : (s:ℝ) ≤ N₁ := by exact_mod_cast hsN
  have hlg0 : 0 ≤ lgSeg p a r := by linarith
  have hY0 : 0 < Y := by linarith
  have c1 : kapSeg p a r s ≤ 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    unfold kapSeg
    have hs3 : (s:ℝ) + 2 ≤ 3 * N₁ := by linarith
    have hrk : (r:ℝ) ≤ (r:ℝ) + 1 := by linarith
    calc 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r
        ≤ 3 * (3 * N₁) * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by gcongr
      _ = _ := by ring
  have c3 : 3 * ((s : ℝ) + 1) * lgSeg p a r + 2 * uSeg p a r t ≤ kapSeg p a r s := by
    unfold uSeg kapSeg
    have h1 : ((t:ℝ)+1)*((r:ℝ)+1) ≤ ((s:ℝ)+1)*((r:ℝ)+1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2' : 2*(r:ℝ) + 5 ≤ 3 * (r:ℝ)^2 := by nlinarith
    have h3 : ((s:ℝ)+1)*(2*(r:ℝ)+5) ≤ ((s:ℝ)+1)*(3*(r:ℝ)^2) := mul_le_mul_of_nonneg_left h2' (by linarith)
    have h5 : 0 ≤ (r:ℝ)^2 := by positivity
    have hc : 0 ≤ 3*((s:ℝ)+2)*(r:ℝ)^2 - (3*((s:ℝ)+1) + 2*(((t:ℝ)+1)*((r:ℝ)+1))) := by nlinarith
    have hm := mul_nonneg hc hlg0
    linarith
  have c2 : Y * firstDepth t Y (kapSeg p a r s) ≤ 36 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    have ht2 : (t:ℝ) + 1 ≤ 2 * N₁ := by linarith
    calc Y * firstDepth t Y (kapSeg p a r s) ≤ Y * (2 * ((t : ℝ) + 1) * Y * kapSeg p a r s) :=
          mul_le_mul_of_nonneg_left hD1 hY0.le
      _ ≤ Y * (2 * (2 * N₁) * Y * (9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r)) := by gcongr
      _ = _ := by ring
  refine ⟨c1, c2, c3, ?_⟩
  unfold DjSeg
  have hfl : ((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ) ≤ Y * firstDepth t Y (kapSeg p a r s) := Int.floor_le _
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hN2 : (N₁:ℝ) ≤ (N₁:ℝ)^2 := le_self_pow₀ hN1 (by norm_num)
  have c4 : 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r ≤ 9 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    calc 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r = 9 * 1 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by ring
      _ ≤ _ := by gcongr
  linarith
end Formalism.CountingSumsFrames
