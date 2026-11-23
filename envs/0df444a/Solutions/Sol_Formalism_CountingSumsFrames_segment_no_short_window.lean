-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_no_short_window
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.102081+00:00
-- url     : https://prove2.me/submissions/b7bf3576-3705-4550-8758-f52253f92e86

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
theorem _root_.solution : SegNoShortWindow := by
  intro p N N₁ r a Y b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  rw [← hk] at h4 ⊢
  have hk3 : 3 ≤ k := by linarith
  have hkY : 0 < k * Y := by positivity
  have h1 : k^2 * Q ≤ (a:ℝ)/(k*Y) := by
    rw [le_div_iff₀ hkY]
    calc k^2*Q*(k*Y) = k^3*Q*Y := by ring
      _ ≤ b' := h4
      _ ≤ a := hba
  refine ⟨h1, ?_⟩
  intro P hP1 hPQ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊(a:ℝ)/(k*Y)⌋₊ + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hlt : (a:ℝ)/(k*Y) < M := by rw [hM]; push_cast; exact Nat.lt_floor_add_one _
  have hPM : P ≤ M := by
    have : (P:ℝ) ≤ M := by
      have h9 : (1:ℝ) ≤ k^2 := one_le_pow₀ (by linarith)
      have : 1 * Q ≤ k^2*Q := mul_le_mul_of_nonneg_right h9 (by linarith)
      linarith
    exact_mod_cast this
  refine ⟨hPM, ?_⟩
  intro Y' hY'
  have hP0 : 0 < P := hP1
  have hq1 : 1 ≤ M / P := (Nat.one_le_div_iff hP0).2 hPM
  have hlt2 : M < P * (M/P + 1) := Nat.lt_mul_div_succ M hP0
  have hle : P * (M/P + 1) ≤ P * (2 * Y') := Nat.mul_le_mul_left _ (by omega)
  have hMr : (M:ℝ) ≤ P * (2 * Y') := by exact_mod_cast (hlt2.le.trans hle)
  refine ⟨by omega, ?_⟩
  have hPr : (0:ℝ) < P := by exact_mod_cast hP0
  rw [div_le_iff₀ (by positivity)]
  have ha := (div_lt_iff₀ hkY).1 hlt
  have := mul_le_mul_of_nonneg_right hMr hkY.le
  calc (a:ℝ) ≤ M * (k*Y) := ha.le
    _ ≤ P * (2 * Y') * (k*Y) := this
    _ = Y' * (2 * k * Y * P) := by ring
end Formalism.CountingSumsFrames
