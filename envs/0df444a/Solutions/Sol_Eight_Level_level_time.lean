-- Prove2me | solution 1 for Eight.Level.level_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:19:55.468209+00:00
-- url     : https://prove2.me/submissions/55880817-abab-411b-a5d3-3219eada35a7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Arith
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Arith
import Theorems.Thm_Eight_Level_Arith_exponent_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork
open Arith
namespace Eight.Level
theorem _root_.solution (g K a A : ℕ) {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (Rn : ℕ) : ∃ A1 : ℕ, ∀ B lam t : ℕ, 1 ≤ lam → 1 ≤ t →
    (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * (((A : ℝ) + 1)
        * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ A * ((a * (B + lam) ^ a * t : ℕ) : ℝ)) + 2
      ≤ (A1 : ℝ) * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) * ((B : ℝ) + lam) ^ A1 * t := by
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℕ, (2 : ℝ) ^ (2 * e * (g : ℝ) ^ 4) ≤ c2 := ⟨_, Nat.le_ceil _⟩
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℕ, c3 = g ^ 3 + g + 2 * g ^ 2 := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℕ, A1 = 2 ^ Rn * (A + 1) * c3 ^ A * a * c2 + 2 + Rn + A + a := ⟨_, rfl⟩
  refine ⟨A1, fun B lam t hlam ht => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = B + lam := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by omega
  have htl : tOf lam ≤ lam := by unfold tOf; omega
  have hYr : (B : ℝ) + lam = (Y : ℝ) := by rw [hY]; push_cast; ring
  have hY1r : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have F0 : (((tOf lam + 1) ^ Rn : ℕ) : ℝ) ≤ ((2 ^ Rn : ℕ) : ℝ) * (Y : ℝ) ^ Rn := by
    have : (tOf lam + 1) ^ Rn ≤ 2 ^ Rn * Y ^ Rn :=
      (Nat.pow_le_pow_left (by omega : tOf lam + 1 ≤ 2 * Y) Rn).trans (le_of_eq (Nat.mul_pow ..))
    exact_mod_cast this
  have f1 : g ^ 3 * lam + (g * B + g ^ 2 * tOf lam) ≤ c3 * Y := by
    have e1 : c3 * Y = g ^ 3 * lam + (g * B + g ^ 2 * lam) + (g ^ 3 * B + g * lam + 2 * g ^ 2 * B + g ^ 2 * lam) := by
      rw [hc3, hY]; ring
    have e2 : g ^ 2 * tOf lam ≤ g ^ 2 * lam := Nat.mul_le_mul_left _ htl
    omega
  have F1 : (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ A ≤ ((c3 ^ A : ℕ) : ℝ) * (Y : ℝ) ^ A := by
    have : (g ^ 3 * lam + (g * B + g ^ 2 * tOf lam)) ^ A ≤ c3 ^ A * Y ^ A :=
      (Nat.pow_le_pow_left f1 A).trans (le_of_eq (Nat.mul_pow ..))
    exact_mod_cast this
  have F2 : ((a * (B + lam) ^ a * t : ℕ) : ℝ) = (a : ℝ) * (Y : ℝ) ^ a * t := by
    rw [← hY]
    push_cast
    ring
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by
    rw [hX]
    have hρ : (0 : ℝ) < rho := by unfold rho; norm_num
    have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hX0 : 0 ≤ X := by linarith
  have F3 : (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) ≤ (c2 : ℝ) * X := by
    calc _ ≤ (2 : ℝ) ^ (2 * e * (g : ℝ) ^ 4 + ((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (exponent_le hK hg h0)
      _ = (2 : ℝ) ^ (2 * e * (g : ℝ) ^ 4) * X := by rw [hX, Real.rpow_add (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc2 hX0
  have F4 : 0 ≤ (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) := by
    positivity
  rw [← hX, hYr, F2]
  generalize (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) = X1 at F3 F4 ⊢
  have hpow : (Y : ℝ) ^ Rn * (Y : ℝ) ^ A * (Y : ℝ) ^ a ≤ (Y : ℝ) ^ A1 := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hY1r (by omega)
  have hYA : (1 : ℝ) ≤ (Y : ℝ) ^ A1 := one_le_pow₀ hY1r
  have hcoef : ((2 ^ Rn * (A + 1) * c3 ^ A * a * c2 : ℕ) : ℝ) + 2 ≤ (A1 : ℝ) := by
    have : 2 ^ Rn * (A + 1) * c3 ^ A * a * c2 + 2 ≤ A1 := by omega
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hone : (1 : ℝ) ≤ X * (Y : ℝ) ^ A1 * t := by
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ X * (Y : ℝ) ^ A1 * t := by gcongr
  calc (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * (((A : ℝ) + 1) * X1
          * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ A * ((a : ℝ) * (Y : ℝ) ^ a * t)) + 2
      = (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((A : ℝ) + 1)
          * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ A * ((a : ℝ) * (Y : ℝ) ^ a * t) * X1 + 2 := by
        ring
    _ ≤ (((2 ^ Rn : ℕ) : ℝ) * (Y : ℝ) ^ Rn) * ((A : ℝ) + 1) * (((c3 ^ A : ℕ) : ℝ) * (Y : ℝ) ^ A)
          * ((a : ℝ) * (Y : ℝ) ^ a * t) * ((c2 : ℝ) * X) + 2 := by gcongr
    _ = ((2 ^ Rn * (A + 1) * c3 ^ A * a * c2 : ℕ) : ℝ) * X * ((Y : ℝ) ^ Rn * (Y : ℝ) ^ A * (Y : ℝ) ^ a) * t + 2 := by
        push_cast; ring
    _ ≤ ((2 ^ Rn * (A + 1) * c3 ^ A * a * c2 : ℕ) : ℝ) * X * (Y : ℝ) ^ A1 * t + 2 * (X * (Y : ℝ) ^ A1 * t) := by
        gcongr
        linarith
    _ = (((2 ^ Rn * (A + 1) * c3 ^ A * a * c2 : ℕ) : ℝ) + 2) * X * (Y : ℝ) ^ A1 * t := by ring
    _ ≤ (A1 : ℝ) * X * (Y : ℝ) ^ A1 * t := by gcongr
end Eight.Level
