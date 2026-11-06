-- Prove2me | solution 1 for CircuitLowerBound.Time.exists_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:59:21.68086+00:00
-- url     : https://prove2.me/submissions/682a35ee-43fe-4b7b-acc4-1282447e0bd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Time
import Theorems.Thm_CircuitLowerBound_Time_final_le
import Theorems.Thm_CircuitLowerBound_Time_base_le
import Theorems.Thm_Groundwork_exists_pow_le


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
open CircuitLowerBound.Time
namespace CircuitLowerBound.Time
theorem _root_.solution (q cE c₀ a₀ G : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n Nv T : ℕ, n ≤ c₀ * (m + 1) → Nv ≤ 3 * n + a₀ * (m + 1) + G →
    (T : ℝ) ≤ cE * (2 : ℝ) ^ (1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ)) * Nv) →
    q * (T + 1) * ((m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1) ^ q ≤ 2 ^ (m / 8) := by
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((cE + 2) * q) (ε := 1 / 32) (by norm_num)
  obtain ⟨Kb, hKb⟩ : ∃ Kb, Kb = (8 + cE) * (3 * c₀ + a₀ + G + 2) ^ (cE + 2) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = q * ((cE + 1) * 2 ^ (G + 1)) * (Kb ^ q * C₁) := ⟨_, rfl⟩
  refine ⟨16 * (K + 1), fun m hm n Nv T hn hNv hT => ?_⟩
  have hb := base_le (cE := cE) hn hNv
  rw [← hKb] at hb
  obtain ⟨base, hbase⟩ : ∃ base, base = (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1 := ⟨_, rfl⟩
  rw [← hbase] at hb ⊢
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (2 : ℝ) ^ ((1 / 32 : ℝ) * m) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  -- the polynomial part
  have h1 : ((base : ℝ)) ^ q ≤ ((Kb ^ q * C₁ : ℕ) : ℝ) * p := by
    have h2 : (base : ℝ) ≤ (Kb : ℝ) * ((m : ℝ) + 2) ^ (cE + 2) := by exact_mod_cast hb
    calc ((base : ℝ)) ^ q ≤ ((Kb : ℝ) * ((m : ℝ) + 2) ^ (cE + 2)) ^ q := by gcongr
      _ = (Kb : ℝ) ^ q * ((m : ℝ) + 2) ^ ((cE + 2) * q) := by rw [mul_pow, ← pow_mul]
      _ ≤ (Kb : ℝ) ^ q * (C₁ * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) := by gcongr; exact hC₁ m
      _ = _ := by rw [hp]; push_cast; ring
  -- the exponential part
  have h3 : (T : ℝ) + 1 ≤ (((cE + 1) * 2 ^ (G + 1) : ℕ) : ℝ) * p := by
    obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 3 * c₀ + a₀ + 1 := ⟨_, rfl⟩
    rw [← hA] at hT
    have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
    have h4 : Nv ≤ A * (m + 1 + G) := by rw [hA]; nlinarith
    have h5 : (Nv : ℝ) ≤ A * ((m : ℝ) + 1 + G) := by exact_mod_cast h4
    have h6 : 1 / (32 * (A : ℝ)) * Nv ≤ (1 / 32 : ℝ) * m + ((G + 1 : ℕ) : ℝ) := by
      have h7 : 1 / (32 * (A : ℝ)) * Nv ≤ 1 / (32 * (A : ℝ)) * (A * ((m : ℝ) + 1 + G)) := mul_le_mul_of_nonneg_left h5 (by positivity)
      have h8 : 1 / (32 * (A : ℝ)) * (A * ((m : ℝ) + 1 + G)) = ((m : ℝ) + 1 + G) / 32 := by field_simp
      have h9 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      push_cast
      linarith
    have h10 : (2 : ℝ) ^ (1 / (32 * (A : ℝ)) * Nv) ≤ p * (2 : ℝ) ^ (G + 1) := by
      rw [hp, ← Real.rpow_natCast 2 (G + 1), ← Real.rpow_add two_pos]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h6
    have h11 : (1 : ℝ) ≤ p * (2 : ℝ) ^ (G + 1) := by
      have h12 : (1 : ℝ) ≤ p := by rw [hp]; exact Real.one_le_rpow one_le_two (by positivity)
      have h13 : (1 : ℝ) ≤ (2 : ℝ) ^ (G + 1) := one_le_pow₀ one_le_two
      nlinarith
    have h14 : (cE : ℝ) * (2 : ℝ) ^ (1 / (32 * (A : ℝ)) * Nv) ≤ cE * (p * (2 : ℝ) ^ (G + 1)) := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have h15 : ((q * (T + 1) * base ^ q : ℕ) : ℝ) ≤ ((2 ^ (m / 8) : ℕ) : ℝ) := by
    calc ((q * (T + 1) * base ^ q : ℕ) : ℝ) = (q : ℝ) * ((T : ℝ) + 1) * (base : ℝ) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * ((((cE + 1) * 2 ^ (G + 1) : ℕ) : ℝ) * p) * (((Kb ^ q * C₁ : ℕ) : ℝ) * p) := by gcongr
      _ = (K : ℝ) * (p * p) := by rw [hK]; push_cast; ring
      _ ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by rw [hp]; exact final_le K hm
      _ = _ := by rw [Real.rpow_natCast]; push_cast; rfl
  exact_mod_cast h15
end CircuitLowerBound.Time
