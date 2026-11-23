-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_hyp_of_interval_hyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:24.247788+00:00
-- url     : https://prove2.me/submissions/2a952c56-f45e-46ca-8f9d-1e88acb7d714

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
theorem _root_.solution : HypSegOfHypI := by
  intro C C₀ hC hC₀ p N N₁ k n' G' Y Yb a b' Ib cl D cStar h
  obtain ⟨hY, hp, hN, hN1, hk, hLa8, hIb1, hIb2, hYb, h2Yb, hab, hde, hpab, hkLa, hcl0, hcl, hD, hcS, hb, hb0⟩ := h
  set La := C₀ * (N₁ : ℝ) ^ 2 * Real.log a with hLadef
  set Q := (p : ℝ) ^ G' with hQdef
  set S := cStar + N * cl + n' * cl with hSdef
  have hC0 : 0 < C := by linarith
  have hC₀0 : 0 < C₀ := by linarith
  have hY0 : 0 < Y := by linarith
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN1r : (1:ℝ) ≤ N₁ := by exact_mod_cast hN1
  have hkr : (5:ℝ) ≤ k := by exact_mod_cast (by omega : 5 ≤ k)
  have hk0 : (0:ℝ) < k := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hk2 : (25:ℝ) ≤ (k:ℝ) ^ 2 := by
    calc (25:ℝ) = 5 ^ 2 := by norm_num
      _ ≤ (k:ℝ) ^ 2 := by gcongr
  have hk3 : (125:ℝ) ≤ (k:ℝ) ^ 3 := by
    calc (125:ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (k:ℝ) ^ 3 := by gcongr
  have hpr : (25:ℝ) ≤ p := by
    calc (25:ℝ) = 25 * 1 := by norm_num
      _ ≤ (k:ℝ) ^ 2 * Y ^ 2 := by gcongr
      _ ≤ p := hp
  have hp0 : (0:ℝ) < p := by linarith
  have hpb : (p:ℝ) * b' < a := (lt_div_iff₀ hb0).mp hpab
  have ha0 : 0 < a := by
    have : 0 < (p:ℝ) * b' := by positivity
    linarith
  have hlogNY : 0 ≤ Real.log (N * Y) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hNr hY)
  have hLa0 : 0 ≤ La := by linarith
  have hc1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 := by
    have : 1 ≤ (N₁:ℝ) ^ 2 := one_le_pow₀ hN1r
    exact one_le_mul_of_one_le_of_one_le hC₀ this
  have hlog0 : 0 ≤ Real.log a := (mul_nonneg_iff_of_pos_left (by linarith : 0 < C₀ * (N₁ : ℝ) ^ 2)).mp hLa0
  have hlogb0 : 0 ≤ Real.logb p a := div_nonneg hlog0 (Real.log_nonneg (by linarith))
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (by positivity) hlogb0) hD
  have hcS8 : 8 ≤ cStar := by linarith
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by linarith)
  have hQ0 : 0 < Q := by linarith
  have hQ4 : Q ≤ Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
  have hS8 : 8 ≤ S := by
    have h1 : 0 ≤ (N:ℝ) * cl := by positivity
    have h2 : 0 ≤ (n':ℝ) * cl := by positivity
    linarith
  have hS0 : 0 < S := by linarith
  have hkQY : (k:ℝ) ^ 3 * Q * Y ≤ b' := by
    calc (k:ℝ) ^ 3 * Q * Y = 1 * (k:ℝ) ^ 3 * 1 * Q * 1 * Y := by ring
      _ ≤ C * (k:ℝ) ^ 3 * N * Q ^ 4 * S * Y := by gcongr; linarith
      _ ≤ b' := hb
  have hb1000 : 1000 ≤ b' := by
    calc (1000:ℝ) = 1 * 125 * 1 * 1 * 8 * 1 := by norm_num
      _ ≤ C * (k:ℝ) ^ 3 * N * Q ^ 4 * S * Y := by gcongr; linarith
      _ ≤ b' := hb
  have ha25 : 25000 < a := by
    have : (25:ℝ) * 1000 ≤ (p:ℝ) * b' := mul_le_mul hpr hb1000 (by norm_num) (by linarith)
    linarith
  have hlog1 : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]
    have := Real.exp_one_lt_d9
    linarith
  have hLalog : Real.log a ≤ La := le_mul_of_one_le_left hlog0 hc1
  have hLa1 : 1 ≤ La := by linarith
  have hLa2 : La ≤ La ^ 2 := le_self_pow₀ hLa1 (by norm_num)
  have hba : b' ≤ a := by
    have : b' ≤ (p:ℝ) * b' := le_mul_of_one_le_left hb0.le (by linarith)
    linarith
  have hLak : La ^ 2 ≤ k := by
    calc La ^ 2 = 1 * 1 * La ^ 2 := by ring
      _ ≤ C * N * La ^ 2 := by gcongr
      _ ≤ k := hkLa
  have hYb1 : 1 ≤ Yb := by linarith
  refine ⟨⟨hY, hp, ?_, ?_, ?_, by linarith, hLa0, by linarith, hkQY, hba, hpab, by omega, hN, hN1, hQ1, hb0⟩, ?_, ?_⟩
  · calc (k:ℝ) * Y ^ 2 * Real.log a = (k:ℝ) * Y ^ 2 * 1 * 1 * 1 * Real.log a := by ring
      _ ≤ (k:ℝ) * Y ^ 2 * Yb * N * La * Real.log a := by gcongr
      _ ≤ a / b' := hab
  · have : (N:ℝ) ≤ k := by
      calc (N:ℝ) = 1 * N * 1 := by ring
        _ ≤ C * N * La ^ 2 := by gcongr; linarith
        _ ≤ k := hkLa
    exact_mod_cast this
  · have h1 : (N₁:ℝ) ^ 2 ≤ La := by
      calc (N₁:ℝ) ^ 2 = 1 * (N₁:ℝ) ^ 2 * 1 := by ring
        _ ≤ C₀ * (N₁:ℝ) ^ 2 * Real.log a := by gcongr
    have h2 : (N₁:ℝ) ^ 4 ≤ La ^ 2 := by
      calc (N₁:ℝ) ^ 4 = ((N₁:ℝ) ^ 2) ^ 2 := by ring
        _ ≤ La ^ 2 := by gcongr
    have : (N₁:ℝ) ^ 4 ≤ k := by linarith
    exact_mod_cast this
  · have : a / (k * Y) ≤ a := div_le_self ha0.le (one_le_mul_of_one_le_of_one_le (by linarith) hY)
    linarith
  · intro bLo bHi h1 h2 h3
    constructor <;> linarith
end Formalism.CountingSumsFrames
