-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.fld_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:14:04.082047+00:00
-- url     : https://prove2.me/submissions/ea3da199-fe27-4b8e-81b2-c364b92b576c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution (W : ℕ) (r : List Bool) : ∀ (X : List ℕ), (∀ x ∈ X, x < 2 ^ W) → ∀ i, i < X.length →
    fld W ((X.map (toWord W)).flatten ++ r) i = X.getD i 0
  | [], _, i, hi => by simp at hi
  | x :: X, h, 0, _ => by
    have : block W 0 (((x :: X).map (toWord W)).flatten ++ r) = toWord W x := by
      simp only [block, Nat.zero_mul, List.drop_zero, List.map_cons, List.flatten_cons, List.append_assoc]
      exact List.take_left' (length_toWord _ _)
    rw [fld, this, ofWord_toWord (h x (by simp))]
    rfl
  | x :: X, h, i + 1, hi => by
    have : block W (i + 1) (((x :: X).map (toWord W)).flatten ++ r) = block W i ((X.map (toWord W)).flatten ++ r) := by
      simp only [block, List.map_cons, List.flatten_cons, List.append_assoc]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (length_toWord _ _)]
    have ih := solution W r X (fun y hy => h y (by simp [hy])) i (by simpa using hi)
    rw [fld] at ih ⊢
    rw [this, ih]
    rfl
end CircuitLowerBound.SmallFacts
