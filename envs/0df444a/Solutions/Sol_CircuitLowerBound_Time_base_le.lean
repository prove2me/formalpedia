-- Prove2me | solution 1 for CircuitLowerBound.Time.base_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:40:12.892042+00:00
-- url     : https://prove2.me/submissions/c2a1c6be-4523-4db5-bead-5c7653f64f36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Time
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
open CircuitLowerBound.Time
namespace CircuitLowerBound.Time
theorem _root_.solution {cE c₀ a₀ G m n Nv : ℕ} (hn : n ≤ c₀ * (m + 1)) (hNv : Nv ≤ 3 * n + a₀ * (m + 1) + G) :
    (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1
      ≤ (8 + cE) * (3 * c₀ + a₀ + G + 2) ^ (cE + 2) * (m + 2) ^ (cE + 2) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (3 * c₀ + a₀ + G + 2) * (m + 2) := ⟨_, rfl⟩
  have h1 : m + 2 ≤ X := by rw [hX]; nlinarith
  have h2 : m + n + 1 ≤ X := by rw [hX]; nlinarith
  have h3 : Nv + 2 ≤ X := by rw [hX]; nlinarith
  have h4 : (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + 1 ≤ 8 * X ^ 2 := by
    have h5 : n * (4 + 2 * (m + n)) ≤ X * (4 + 2 * X) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have h6 : X ^ 2 ≤ X ^ (cE + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h7 : (Nv + 2) ^ cE ≤ X ^ (cE + 2) := (Nat.pow_le_pow_left h3 cE).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h8 := Nat.mul_le_mul_left cE h7
  rw [mul_assoc, ← mul_pow, ← hX, add_mul]
  omega
end CircuitLowerBound.Time
