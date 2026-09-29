-- Prove2me | solution 1 for DivisorBounds.tau_factor_small
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:54:19.243212+00:00
-- url     : https://prove2.me/submissions/f97f007f-86d9-4f41-bf89-da8d233a1b1d

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.TauSpike =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The elementary divisor bound `τ(n) ≪_ε n^ε`

For every `ε > 0` there is a constant `C` with `τ(n) ≤ C · n^ε` for all `n ≥ 1`,
where `τ(n) = n.divisors.card` is the number-of-divisors function.  This is the
classical elementary estimate: writing `τ(n) = ∏_{p^a ‖ n} (a+1)` and
`n^ε = ∏_{p^a ‖ n} p^{aε}`, the ratio `τ(n)/n^ε = ∏ (a+1)/p^{aε}` factors, and
each factor with `p^ε ≥ 2` is `≤ 1` while the (boundedly many) small primes
`p < 2^{1/ε}` each contribute at most the fixed constant `1 + 1/(ε·log 2)`.

The main statement is `Salt.Maynard.card_divisors_le_rpow`.  The right-hand side
uses `Real.rpow` (`(n : ℝ) ^ ε`), matching the growth-bound convention in the
`Salt/Maynard/` corpus.
-/

namespace Salt.Maynard

open Finset

/-- Large-prime factor bound: when `p^ε ≥ 2` (i.e. `p` is above the threshold),
the local factor `(a+1)` is dominated by `p^{aε}` with constant `1`.  Uses only
`p ≥ 2` and `2^a ≥ a+1`. -/
lemma tau_factor_large {p a : ℕ} {ε : ℝ} (hpe : (2 : ℝ) ≤ (p : ℝ) ^ ε) :
    (a : ℝ) + 1 ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have key : (p : ℝ) ^ ((a : ℝ) * ε) = ((p : ℝ) ^ ε) ^ a := by
    rw [mul_comm, Real.rpow_mul hp0, Real.rpow_natCast]
  rw [key]
  have h2a : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ ε) ^ a :=
    pow_le_pow_left₀ (by norm_num) hpe a
  have hlt : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
    have h : a < 2 ^ a := Nat.lt_two_pow_self
    have hc : (a : ℝ) + 1 ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast h
    simpa using hc
  linarith

/-- Small-prime factor bound: for any prime power the local factor `(a+1)` is at
most `(1 + 1/(ε·log 2)) · p^{aε}`.  This is the calculus estimate
`a + 1 ≤ (1 + 1/(ε log 2)) · 2^{aε}` combined with `2 ≤ p`. -/
lemma tau_factor_small {p a : ℕ} {ε : ℝ} (hε : 0 < ε) (hp2 : 2 ≤ p) :
    (a : ℝ) + 1 ≤ (1 + (ε * Real.log 2)⁻¹) * (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := ε * Real.log 2 with hK
  have hKpos : (0 : ℝ) < K := mul_pos hε hlog2
  -- `2^{aε} = exp (K · a)`
  have hrpow : (2 : ℝ) ^ ((a : ℝ) * ε) = Real.exp (K * (a : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hK]; ring
  -- `a + 1 ≤ (1 + K⁻¹) · exp (K·a)`
  have e1 : K * (a : ℝ) ≤ Real.exp (K * (a : ℝ)) := by
    linarith [Real.add_one_le_exp (K * (a : ℝ))]
  have e2 : (1 : ℝ) ≤ Real.exp (K * (a : ℝ)) :=
    Real.one_le_exp (mul_nonneg hKpos.le (by positivity))
  have hKinv : (0 : ℝ) ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hle1 : (a : ℝ) ≤ K⁻¹ * Real.exp (K * (a : ℝ)) := by
    have hmul : (a : ℝ) * K ≤ Real.exp (K * (a : ℝ)) := by
      rw [mul_comm]; exact e1
    have h2 := mul_le_mul_of_nonneg_left hmul hKinv
    rwa [mul_comm (a : ℝ) K, ← mul_assoc, inv_mul_cancel₀ hKpos.ne', one_mul] at h2
  have step1 : (a : ℝ) + 1 ≤ (1 + K⁻¹) * (2 : ℝ) ^ ((a : ℝ) * ε) := by
    rw [hrpow]
    calc (a : ℝ) + 1
        ≤ K⁻¹ * Real.exp (K * (a : ℝ)) + Real.exp (K * (a : ℝ)) := by linarith
      _ = (1 + K⁻¹) * Real.exp (K * (a : ℝ)) := by ring
  -- upgrade `2` to `p`
  have hmono : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ (p : ℝ) ^ ((a : ℝ) * ε) :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) (by positivity)
  have hg0 : (0 : ℝ) ≤ 1 + K⁻¹ := by linarith
  calc (a : ℝ) + 1 ≤ (1 + K⁻¹) * (2 : ℝ) ^ ((a : ℝ) * ε) := step1
    _ ≤ (1 + K⁻¹) * (p : ℝ) ^ ((a : ℝ) * ε) := mul_le_mul_of_nonneg_left hmono hg0

/-- Threshold lemma: any `p ≥ ⌈2^{1/ε}⌉` satisfies `p^ε ≥ 2`. -/
lemma tau_threshold {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : ⌈(2 : ℝ) ^ ε⁻¹⌉₊ ≤ p) :
    (2 : ℝ) ≤ (p : ℝ) ^ ε := by
  have h1 : (2 : ℝ) ^ ε⁻¹ ≤ (p : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hp)
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ε⁻¹ := Real.rpow_nonneg (by norm_num) _
  calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
    _ = (2 : ℝ) ^ (ε⁻¹ * ε) := by rw [inv_mul_cancel₀ hε.ne']
    _ = ((2 : ℝ) ^ ε⁻¹) ^ ε := Real.rpow_mul (by norm_num) _ _
    _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow h2 h1 hε.le

/-- **The elementary divisor bound.** For every `ε > 0` there is a constant `C > 0`
with `τ(n) = #n.divisors ≤ C · n^ε` for all `n ≥ 1`. -/
theorem card_divisors_le_rpow :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < ε * Real.log 2 := mul_pos hε hlog2
  set g : ℝ := 1 + (ε * Real.log 2)⁻¹ with hg
  set P₀ : ℕ := ⌈(2 : ℝ) ^ ε⁻¹⌉₊ with hP₀
  have hg1 : (1 : ℝ) ≤ g := by rw [hg]; have := (inv_pos.mpr hKpos).le; linarith
  have hgpos : (0 : ℝ) < g := by rw [hg]; have := inv_pos.mpr hKpos; linarith
  refine ⟨g ^ P₀, pow_pos hgpos P₀, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  -- `n = ∏_{p | n} p^{a_p}` in `ℝ`
  have hn_eq : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    have h1 : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
    calc (n : ℝ)
        = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p) : ℕ) : ℝ) := by rw [← h1]
      _ = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by push_cast; rfl
  -- `∏_{p | n} p^{a_p ε} = n^ε`
  have hq : ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε)
      = (n : ℝ) ^ ε := by
    rw [hn_eq, ← Real.finsetProd_rpow n.primeFactors
        (fun p => (p : ℝ) ^ (n.factorization p)) (fun p _ => by positivity) ε]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul (by positivity)]
  -- per-factor bound
  have hfactor : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1)
        ≤ (if p < P₀ then g else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hlt : p < P₀
    · rw [if_pos hlt, hg]; exact tau_factor_small hε hp2
    · rw [if_neg hlt, one_mul]
      exact tau_factor_large (tau_threshold hε (hP₀ ▸ not_lt.mp hlt))
  -- the constant product `∏ c_p ≤ g^{P₀}`
  have hprodc : ∏ p ∈ n.primeFactors, (if p < P₀ then g else 1 : ℝ) ≤ g ^ P₀ := by
    have hrw : ∏ p ∈ n.primeFactors, (if p < P₀ then g else 1 : ℝ)
        = ∏ _p ∈ n.primeFactors.filter (· < P₀), g :=
      (Finset.prod_filter (· < P₀) (fun _ => (g : ℝ))).symm
    rw [hrw, Finset.prod_const]
    apply pow_le_pow_right₀ hg1
    calc (n.primeFactors.filter (· < P₀)).card
        ≤ (Finset.range P₀).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
      _ = P₀ := Finset.card_range P₀
  -- assemble
  rw [Nat.card_divisors hn0]
  push_cast
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          (if p < P₀ then g else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, (if p < P₀ then g else 1))
          * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_mul_distrib
    _ ≤ g ^ P₀ * (n : ℝ) ^ ε := by
        rw [hq]; exact mul_le_mul_of_nonneg_right hprodc (by positivity)

end Salt.Maynard

end




section
open Finset

theorem solution {p a : ℕ} {ε : ℝ} (hε : 0 < ε) (hp2 : 2 ≤ p) :
    (a : ℝ) + 1 ≤ (1 + (ε * Real.log 2)⁻¹) * (p : ℝ) ^ ((a : ℝ) * ε) := by
  apply Salt.Maynard.tau_factor_small <;> assumption

end

