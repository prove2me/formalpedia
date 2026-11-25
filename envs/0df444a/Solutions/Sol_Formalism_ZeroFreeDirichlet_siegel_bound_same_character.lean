-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.siegel_bound_same_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:01.841646+00:00
-- url     : https://prove2.me/submissions/de49c7ae-d804-430f-91e0-85fd0392fd44

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {N₀ : ℕ} (hN₀ : N₀ ≠ 0) {A₁ x ε q₁ q : ℝ} (hε : 0 < ε) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) (hNq : (N₀ : ℝ) = q₁ * q) (hA₁ : 0 < A₁) (hx : 0 ≤ x)
    (hS : A₁ ≤ ((N₀.primeFactors.card : ℝ) + 1) ^ 2 * x) :
    A₁ / (4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set ω := N₀.primeFactors.card with hω

  have hpow : 2 ^ ω ≤ N₀ := by
    have h1 := Finset.pow_card_le_prod N₀.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₀) (Nat.prod_primeFactors_dvd N₀))
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast Nat.pos_of_ne_zero hN₀
  have hpowR : (2 : ℝ) ^ ω ≤ (N₀ : ℝ) := by exact_mod_cast hpow
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hωlog : (ω : ℝ) * Real.log 2 ≤ Real.log N₀ := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpowR
  have hlog2N : Real.log (2 * N₀) = Real.log 2 + Real.log N₀ := Real.log_mul (by norm_num) hN0.ne'
  have hbound := Real.log_le_rpow_div (x := 2 * (N₀ : ℝ)) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN0.le] at hbound
  set R := (2 : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) / (ε / 2) with hR
  have hωR : ((ω : ℝ) + 1) * Real.log 2 ≤ R := by nlinarith
  have hω0 : (0 : ℝ) ≤ (ω : ℝ) + 1 := by positivity
  have hsq : (((ω : ℝ) + 1) * Real.log 2) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hωR 2
  have hR2 : R ^ 2 = 4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε) := by
    have e1 : (2 : ℝ) ^ (ε / 2) * (2 : ℝ) ^ (ε / 2) = (2 : ℝ) ^ ε := by
      rw [← Real.rpow_add (by norm_num), add_halves]
    have e2 : (N₀ : ℝ) ^ (ε / 2) * (N₀ : ℝ) ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
      rw [← Real.rpow_add hN0, add_halves, hNq, Real.mul_rpow (by linarith) (by linarith)]
    rw [hR, div_pow, mul_pow, sq ((2 : ℝ) ^ (ε / 2)), sq ((N₀ : ℝ) ^ (ε / 2)), e1, e2]
    field_simp
    ring
  have hT : ((ω : ℝ) + 1) ^ 2 ≤ 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε := by
    have hl22 : 0 < Real.log 2 ^ 2 := by positivity
    rw [mul_pow, hR2] at hsq
    have e : 4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε * q ^ ε
        = (4 / ε ^ 2 * (2 : ℝ) ^ ε * (q₁ ^ ε * q ^ ε)) / Real.log 2 ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ hl22]
    exact hsq
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hT hx
  nlinarith
end Formalism.ZeroFreeDirichlet
