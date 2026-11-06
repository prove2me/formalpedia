-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.bits_foldr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:56.759204+00:00
-- url     : https://prove2.me/submissions/2381e0d4-1a6c-418d-8636-b8fe0c8b3eee

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
theorem _root_.solution (w : List Bool) : Nat.bits ((w ++ [true]).foldr Nat.bit 0) = w ++ [true] := by
  induction w with
  | nil => simp [Nat.bit]
  | cons b w ih =>
    rw [List.cons_append, List.foldr_cons, Nat.bits_append_bit _ _ fun h => ?_, ih]
    rw [h] at ih
    simp at ih
end CircuitLowerBound.SmallFacts
