-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.nu_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:11:07.678304+00:00
-- url     : https://prove2.me/submissions/a7e4e74c-df6b-43f9-936c-a7b7bd807154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_nu_two_mul
import Theorems.Thm_CircuitLowerBound_SmallFacts_nu_odd
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
theorem _root_.solution (a s : ℕ) : nu (2 ^ a * (2 * s + 1)) = a := by
  induction a with
  | zero => simpa using nu_odd s
  | succ a ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, nu_two_mul (by positivity), ih]
end CircuitLowerBound.SmallFacts
