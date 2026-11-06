-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.nu_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:33.257841+00:00
-- url     : https://prove2.me/submissions/7369cf42-dd8b-48dc-be97-88f48446725c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) : nu (2 * k) = nu k + 1 := by
  have : Nat.bits (2 * k) = false :: Nat.bits k := by
    rw [← Nat.bit_false_apply, Nat.bits_append_bit _ _ fun h => absurd h hk]
  simp [nu, this]
end CircuitLowerBound.SmallFacts
