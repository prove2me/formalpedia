-- Prove2me | solution 1 for Eight.ViaGrouping.Correct.absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:54.784368+00:00
-- url     : https://prove2.me/submissions/d0bfbf60-21ca-4d9a-a67b-927f4c818fe5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
namespace Correct
theorem _root_.solution {NA : NetAlg} {K : ℕ} {ε b : ℝ} (h : Correct NA g K ε b) :
    ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B t S : ℕ), IsNetworkP Np c N P (B + 1) t (S + 2) →
      ∃ T : ℕ, (NA.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t := by
  obtain ⟨A₀, hA₀⟩ := h
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = A₀ * 2 ^ A₀ + 2 := ⟨_, rfl⟩
  have hA₀A : A₀ ≤ A := by
    have : A₀ * 1 ≤ A₀ * 2 ^ A₀ := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    omega
  refine ⟨A, fun C _ Np c N P B t S hN => ?_⟩
  have hP : 1 ≤ P := hN.is.P_pos
  obtain ⟨T, hrun, hT⟩ := hA₀ C Np c N P (B + 1) t _ hN
  refine ⟨T, hrun.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = size c + P + B := ⟨_, rfl⟩
    have e0 : size c + P + (B + 1) = Z + 1 := by omega
    rw [e0, ← hZ]
    have hZ1 : 1 ≤ Z := by omega
    have h1 : (Z + 1) ^ A₀ ≤ 2 ^ A₀ * Z ^ A := by
      calc (Z + 1) ^ A₀ ≤ (2 * Z) ^ A₀ := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ A₀ * Z ^ A₀ := mul_pow _ _ _
        _ ≤ 2 ^ A₀ * Z ^ A := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 hA₀A)
    have h2 : 1 ≤ Z ^ A := Nat.one_le_pow _ _ hZ1
    have h5 : A₀ * (Z + 1) ^ A₀ ≤ A₀ * (2 ^ A₀ * Z ^ A) := Nat.mul_le_mul_left _ h1
    have e : A * Z ^ A = A₀ * (2 ^ A₀ * Z ^ A) + 2 * Z ^ A := by rw [hA]; ring
    omega
  · -- the number of steps
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) := ⟨_, rfl⟩
    rw [← hX] at hT ⊢
    have hX0 : 0 ≤ X := hX ▸ (Real.rpow_pos_of_pos (by norm_num) _).le
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hY2 : (P : ℝ) + ((B + 1 : ℕ) : ℝ) ≤ 2 * ((P : ℝ) + B) := by push_cast; linarith
    have hY0 : (0 : ℝ) ≤ (P : ℝ) + ((B + 1 : ℕ) : ℝ) := by positivity
    have hYp : ((P : ℝ) + B) ^ A₀ ≤ ((P : ℝ) + B) ^ A := pow_le_pow_right₀ hY hA₀A
    have hAC : (A₀ : ℝ) * 2 ^ A₀ ≤ A := by exact_mod_cast (by omega : A₀ * 2 ^ A₀ ≤ A)
    calc (T : ℝ) ≤ A₀ * X * ((P : ℝ) + ((B + 1 : ℕ) : ℝ)) ^ A₀ * t := hT
      _ ≤ A₀ * X * (2 * ((P : ℝ) + B)) ^ A₀ * t := by gcongr
      _ = A₀ * 2 ^ A₀ * X * ((P : ℝ) + B) ^ A₀ * t := by rw [mul_pow]; ring
      _ ≤ A * X * ((P : ℝ) + B) ^ A * t := by gcongr
end Correct
end Eight.ViaGrouping
