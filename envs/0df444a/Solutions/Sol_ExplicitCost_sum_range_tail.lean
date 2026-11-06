-- Prove2me | solution 1 for ExplicitCost.sum_range_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:44.124214+00:00
-- url     : https://prove2.me/submissions/0cf5b3ee-2abe-4653-9a5a-22fe8cd6ae1c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_sum_range_eq_list
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]
namespace ExplicitCost
theorem _root_.solution (n : ℕ → ℕ) (m κ : ℕ) (h : ∀ k, m ≤ k → n k = n m) : ∑ i ∈ Finset.range κ, n i = ((List.range (min κ m)).map n).sum + (κ - m) * n m := by
  rw [← sum_range_eq_list]
  rcases le_total κ m with h1 | h1
  · rw [min_eq_left h1, Nat.sub_eq_zero_of_le h1, Nat.zero_mul, Nat.add_zero]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
    rw [min_eq_right h1, Nat.add_sub_cancel_left, Finset.sum_range_add, Finset.sum_congr rfl fun i _ => h (m + i) (Nat.le_add_right _ _), Finset.sum_const, Finset.card_range, smul_eq_mul]
end ExplicitCost
