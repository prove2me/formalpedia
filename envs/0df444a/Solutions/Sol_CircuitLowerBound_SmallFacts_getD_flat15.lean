-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.getD_flat15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:14:17.704011+00:00
-- url     : https://prove2.me/submissions/460a9c84-5389-4474-b272-8200f4f303ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_n15
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
theorem _root_.solution : ∀ (X : List TCl) (r i : ℕ), r < X.length → i < 15 → ((X.map n15).flatten).getD (15 * r + i) 0 = (n15 (X.getD r zeroCl)).getD i 0
  | [], r, i, hr, _ => by simp at hr
  | c :: X, 0, i, _, hi => by
    rw [List.map_cons, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [length_n15]; exact hi)]
    rfl
  | c :: X, r + 1, i, hr, hi => by
    rw [List.map_cons, List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [length_n15]; omega), length_n15,
      show 15 * (r + 1) + i - 15 = 15 * r + i by omega, solution X r i (by simpa using hr) hi]
    rfl
end CircuitLowerBound.SmallFacts
