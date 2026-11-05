-- Prove2me | solution 1 for CircuitLowerBound.stChain
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:22:55.53552+00:00
-- url     : https://prove2.me/submissions/53430ca0-caec-4f43-97c0-19f0eaf6d1d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts

private theorem stChain_nu_two_mul {k : ℕ} (hk : k ≠ 0) : nu (2 * k) = nu k + 1 := by
  have : Nat.bits (2 * k) = false :: Nat.bits k := by
    rw [← Nat.bit_false_apply, Nat.bits_append_bit _ _ fun h => absurd h hk]
  simp [nu, this]

private theorem stChain_nu_odd (s : ℕ) : nu (2 * s + 1) = 0 := by
  simp [nu]

private theorem stChain_nu_pow_mul (a s : ℕ) : nu (2 ^ a * (2 * s + 1)) = a := by
  induction a with
  | zero => simpa using stChain_nu_odd s
  | succ a ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, stChain_nu_two_mul (by positivity), ih]

theorem solution : StChain := fun a s => by
  have h := stChain_nu_pow_mul a s
  refine ⟨h, ?_⟩
  rw [pos, h, Nat.mul_div_cancel_left _ (by positivity)]
  omega
