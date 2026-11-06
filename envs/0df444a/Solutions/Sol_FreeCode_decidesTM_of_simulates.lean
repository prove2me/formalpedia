-- Prove2me | solution 1 for FreeCode.decidesTM_of_simulates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:52.869199+00:00
-- url     : https://prove2.me/submissions/476de4fb-e364-4e05-8b02-aed9d10c4550

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
import Theorems.Thm_FreeCode_overhead_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_exists_pow_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : DecidesFree Ms w (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatFree.DecidesTM w M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨G, hG⟩ : ∃ G, G = (2 ^ w * (w + 1) + 2 + c) ^ q := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((w + 1 + c) * q) hδ2
  refine ⟨q * (c + 1) * (G * C₁) + c, Nat.le_add_left _ _, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨ev⟩ := hs _ b T _ hr
  have hpow := overhead_le h3 c q
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q := ⟨_, rfl⟩
  rw [← hY, ← hG] at hpow
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((w + 1 + c) * q) := by exact_mod_cast hpow
      exact h5.trans (mul_le_mul_of_nonneg_left hCn (Nat.cast_nonneg _))
    have h7 : (2 : ℝ) ^ (δ * n) = E * E := by
      rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
    have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hEE : (0 : ℝ) ≤ E * E := by positivity
    push_cast
    rw [h7]
    calc (q : ℝ) * ((T : ℝ) + 1) * (Y : ℝ) ≤ (q : ℝ) * (((c : ℝ) + 1) * E) * ((G : ℝ) * (C₁ * E)) := by gcongr
      _ = ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁)) * (E * E) := by ring
      _ ≤ ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁) + c) * (E * E) := mul_le_mul_of_nonneg_right (by linarith) hEE
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩
end FreeCode
