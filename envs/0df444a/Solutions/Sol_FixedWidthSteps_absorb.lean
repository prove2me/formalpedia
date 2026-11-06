-- Prove2me | solution 1 for FixedWidthSteps.absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:23:09.8049+00:00
-- url     : https://prove2.me/submissions/ee27dfa0-29e8-4e8d-b957-5ecffddbf1b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_FixedWidthSteps_Absorb
import Theorems.Thm_FixedWidthSteps_pow_eq_two_rpow
import Theorems.Thm_FixedWidthSteps_expVariables_pos
import Theorems.Thm_FixedWidthSteps_lg_facts
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution (α : ℝ) {c₁ : ℕ} (hc : 1 ≤ c₁) (hB : ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n) (q D : ℕ) {n t X : ℕ} (hn : 4 ≤ n)
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * expVariables α n)) (hX : X + 1 ≤ (n + 2) ^ D) : q * (t + X + 1) ^ q ≤ timeVariables α (q * (2 * D + 2) * c₁) n := by
  obtain ⟨hl2, -⟩ := lg_facts hn
  have hE := expVariables_pos α hn
  have hBn := hB n hn
  unfold timeVariables
  apply Nat.le_floor
  generalize expVariables α n = E at *
  have hc' : (1 : ℝ) ≤ c₁ := by exact_mod_cast hc
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = c₁ * E := ⟨_, rfl⟩
  rw [← hy] at hBn
  have hEy : E ≤ y := by rw [hy]; nlinarith
  have hy1 : 1 ≤ y := by linarith
  have ht' : (t : ℝ) ≤ (2 : ℝ) ^ (2 * (D : ℝ) * y) :=
    ht.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith [mul_le_mul_of_nonneg_left hEy hD, mul_nonneg hD (by linarith : (0 : ℝ) ≤ y)]))
  have hX' : (X : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * (D : ℝ) * y) := by
    have h1 : (X : ℝ) + 1 ≤ ((n : ℝ) + 2) ^ D := by exact_mod_cast hX
    have h2 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc (X : ℝ) + 1 ≤ ((n : ℝ) + 2) ^ D := h1
      _ ≤ ((n : ℝ) ^ 2) ^ D := pow_le_pow_left₀ (by positivity) h2 D
      _ = (2 : ℝ) ^ (2 * (D : ℝ) * lg n) := by rw [← pow_mul, pow_eq_two_rpow (x := (n : ℝ)) (by linarith), Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hBn (by positivity))
  have hsum : (t : ℝ) + X + 1 ≤ (2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y) := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ y := by
      have := Real.rpow_le_rpow_of_exponent_le (one_le_two (α := ℝ)) hy1
      rwa [Real.rpow_one] at this
    have e : (2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y) = (2 : ℝ) ^ y * (2 : ℝ) ^ (2 * (D : ℝ) * y) := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hp : 0 < (2 : ℝ) ^ (2 * (D : ℝ) * y) := by positivity
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right h2 hp.le]
  have hpow : ((t : ℝ) + X + 1) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * ((2 * (D : ℝ) + 1) * y)) := by
    calc ((t : ℝ) + X + 1) ^ q ≤ ((2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y)) ^ q := pow_le_pow_left₀ (by positivity) hsum q
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  have hq : (q : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) * y) := by
    calc (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast Nat.lt_two_pow_self.le
      _ = (2 : ℝ) ^ (q : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
  push_cast
  calc (q : ℝ) * ((t : ℝ) + X + 1) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * y) * (2 : ℝ) ^ ((q : ℝ) * ((2 * (D : ℝ) + 1) * y)) := mul_le_mul hq hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), hy]; congr 1; ring
end FixedWidthSteps
