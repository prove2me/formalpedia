-- Prove2me | solution 1 for Esgk.eventual_one_fifth_excess_of_nat_deficiency_quintic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:13:42.008983+00:00
-- url     : https://prove2.me/submissions/ad59a302-1ef7-411f-b491-d581f68aa653

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

open Filter

theorem solution
    (X : ℕ → Type)
    (P : (n : ℕ) → X n → Prop)
    (K : (n : ℕ) → X n → ℕ)
    (hquintic :
      ∃ A : ℕ, 0 < A ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ x : X n,
            P n x →
            ∃ σ : ℕ, (n - 1) + σ = 3 * K n x ∧ n ≤ A * (σ + 1) ^ 5) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X n,
          P n x →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 5 : ℝ) ≤ (K n x : ℝ) := by
  obtain ⟨A, hA, hev⟩ := hquintic
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have h6 : (0 : ℝ) < 6 * (A : ℝ) := by linarith
  -- `A ≤ A ^ 5` (the source of the fifth-root loss).
  have hA5 : A ≤ A ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hA (by omega : 1 ≤ 5)
  refine ⟨1 / (6 * (A : ℝ)), div_pos one_pos h6, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop ((4 * A) ^ 5),
    Filter.eventually_ge_atTop 1] with n hn hnbig hn1 x hx
  obtain ⟨σ, hσeq, hσb⟩ := hn x hx
  show (n : ℝ) / 3 + 1 / (6 * (A : ℝ)) * ((n : ℝ) ^ (1 / 5 : ℝ)) ≤ (K n x : ℝ)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hn0 _
  -- The fifth power of the fifth root is the original number.
  have hy5 : ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hn0]
    norm_num
  -- Lower bound on the fifth root, from `n ≥ (4A)^5`.
  have h4R : ((4 : ℝ) * (A : ℝ)) ^ (5 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hnbig
  have hy4 : 4 * (A : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hpow : ((4 : ℝ) * (A : ℝ)) ^ (5 : ℕ) ≤ ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) := by
      rw [hy5]; exact h4R
    exact le_of_pow_le_pow_left₀ (by norm_num) hy0 hpow
  -- Upper bound on the fifth root, from the quintic deficiency bound.
  have hnat : n ≤ (A * (σ + 1)) ^ 5 := by
    calc n ≤ A * (σ + 1) ^ 5 := hσb
      _ ≤ A ^ 5 * (σ + 1) ^ 5 := Nat.mul_le_mul hA5 le_rfl
      _ = (A * (σ + 1)) ^ 5 := (mul_pow _ _ _).symm
  have hnatR : (n : ℝ) ≤ ((A : ℝ) * ((σ : ℝ) + 1)) ^ (5 : ℕ) := by exact_mod_cast hnat
  have hyA : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (A : ℝ) * ((σ : ℝ) + 1) := by
    have hpow : ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) ≤ ((A : ℝ) * ((σ : ℝ) + 1)) ^ (5 : ℕ) := by
      rw [hy5]; exact hnatR
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow
  -- Combine: `y ≤ Aσ + A` and `4A ≤ y` give `y ≤ 2Aσ - 2A`.
  have key : (n : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (A : ℝ) * (σ : ℝ) - 2 * (A : ℝ) := by
    linarith [hyA, hy4]
  -- The exact deficiency identity, transported to `ℝ`.
  have hcast : (n : ℝ) - 1 + (σ : ℝ) = 3 * (K n x : ℝ) := by
    have hcs : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    have h2 : ((n - 1 : ℕ) : ℝ) + (σ : ℝ) = 3 * (K n x : ℝ) := by exact_mod_cast hσeq
    rw [hcs] at h2
    exact h2
  have hcy : 1 / (6 * (A : ℝ)) * ((n : ℝ) ^ (1 / 5 : ℝ)) ≤ ((σ : ℝ) - 1) / 3 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h6 (by norm_num : (0 : ℝ) < 3)]
    linarith [key]
  calc (n : ℝ) / 3 + 1 / (6 * (A : ℝ)) * ((n : ℝ) ^ (1 / 5 : ℝ))
      ≤ (n : ℝ) / 3 + ((σ : ℝ) - 1) / 3 := by linarith [hcy]
    _ = (K n x : ℝ) := by linarith [hcast]
