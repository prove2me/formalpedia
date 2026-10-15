-- Prove2me | solution 1 for Esgk.eventually_fourth_root_excess_of_quartic_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-15T06:19:56.335005+00:00
-- url     : https://prove2.me/submissions/828afcd2-0336-4777-9afd-4009e1f73ac8

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

set_option autoImplicit false

/-!
# Fourth-root assembly from a quartic deficiency bound

This module isolates the numerical implication used by the fourth-root distance
argument. The geometric producer remains a separate explicit obligation.
-/

open Filter


private lemma fourth_root_le_mul {n s A : ℕ} (hA : 0 < A)
    (hn : n ≤ A * (s + 1) ^ 4) :
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (A + 1 : ℕ) * (s + 1) := by
  let B : ℕ := A + 1
  have hAB : A ≤ B := by simp [B]
  have hBpow : B ≤ B ^ 4 := Nat.le_pow (by norm_num)
  have hApow : A ≤ B ^ 4 := hAB.trans hBpow
  have hmul : A * (s + 1) ^ 4 ≤ B ^ 4 * (s + 1) ^ 4 :=
    Nat.mul_le_mul_right _ hApow
  have hpow : B ^ 4 * (s + 1) ^ 4 = (B * (s + 1)) ^ 4 := by
    rw [Nat.mul_pow]
  have hnat : n ≤ (B * (s + 1)) ^ 4 := hn.trans (hmul.trans_eq hpow)
  have hreal : (n : ℝ) ≤ ((B * (s + 1)) ^ 4 : ℕ) := by exact_mod_cast hnat
  have hroot := Real.rpow_le_rpow (show 0 ≤ (n : ℝ) by positivity) hreal
    (by norm_num : 0 ≤ (1 / 4 : ℝ))
  rw [Nat.cast_pow] at hroot
  rw [show (1 / 4 : ℝ) = (↑(4 : ℕ))⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at hroot
  simpa [B] using hroot

/-- A uniform quartic inequality for the deficiency yields a fourth-root excess.

The premise is deliberately abstract in the family of admissible objects and
predicate, so the numerical assembly can be consumed directly by the geometric
distance theorem.
-/
theorem solution
    {P : ℕ → Type} {Q : ∀ n, P n → Prop} {K : ∀ n, P n → ℕ}
    (hA : ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p → ∃ σ : ℕ,
        (n - 1) + σ = 3 * K n p ∧ n ≤ A * (σ + 1) ^ 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p →
      (n : ℝ) / 3 + c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ K n p := by
  obtain ⟨A, hA, hbound⟩ := hA
  let B : ℕ := A + 1
  let c : ℝ := 1 / (6 * (B : ℝ))
  have hBpos : 0 < B := by simp [B]
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound, (Filter.eventually_ge_atTop ((4 * B) ^ 4 : ℕ))] with n hn hlarge p hp
  obtain ⟨σ, hsigma, hquartic⟩ := hn p hp
  let s : ℕ := σ + 1
  have hsroot : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (B : ℝ) * s := by
    simpa [B, s] using fourth_root_le_mul hA hquartic
  have hlarge' : (4 * (B : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have hncast : ((4 * B) ^ 4 : ℕ) ≤ n := hlarge
    have hnr : (((4 * B) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hncast
    have hpowroot := Real.rpow_le_rpow (show 0 ≤ (((4 * B) ^ 4 : ℕ) : ℝ) by positivity)
      hnr (by norm_num : 0 ≤ (1 / 4 : ℝ))
    rw [Nat.cast_pow] at hpowroot
    rw [show (1 / 4 : ℝ) = (↑(4 : ℕ))⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at hpowroot
    simpa [mul_pow] using hpowroot
  have hsroot_comm : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (s : ℝ) * (B : ℝ) := by
    simpa [mul_comm] using hsroot
  have hsexcess : (2 : ℝ) + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤ (s : ℝ) := by
    have hsroot' : (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) ≤ s :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < B)).2 hsroot_comm
    have hhalf : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B)).2
      linarith [hlarge']
    have haux : 2 + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤
        (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) := by
      calc
        2 + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤
            (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) +
              (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) := by linarith
        _ = (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) := by ring
    exact haux.trans hsroot'
  have hrelr0 : ((n - 1 : ℕ) : ℝ) + (σ : ℝ) = ((3 * K n p : ℕ) : ℝ) := by
    exact_mod_cast hsigma
  have hrelr : ((n : ℝ) - 1) + (σ : ℝ) = 3 * (K n p : ℝ) := by
    have hbasepos : 0 < 4 * B := by omega
    have hbase : 1 ≤ (4 * B) ^ 4 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hbasepos))
    have hn1 : 1 ≤ n := hbase.trans hlarge
    rw [Nat.cast_sub hn1] at hrelr0
    norm_num at hrelr0 ⊢
    exact hrelr0
  have hmain : (n : ℝ) / 3 + c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ (K n p : ℝ) := by
    dsimp [c, s] at hsexcess ⊢
    norm_num [div_eq_mul_inv] at hsexcess ⊢
    linarith
  exact hmain

