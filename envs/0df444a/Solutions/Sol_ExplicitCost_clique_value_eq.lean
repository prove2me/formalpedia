-- Prove2me | solution 1 for ExplicitCost.clique_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:42.052259+00:00
-- url     : https://prove2.me/submissions/63e6cd86-b313-4ff7-a14a-6a0804c869bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Within
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Brute
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Printed_flatten_copies
import Theorems.Thm_Printed_stCliqueValue
import Theorems.Thm_Value_stCliqueValue
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => W w.val).value = Paper.cliqueValue lam (listTables K W) := by
  refine (Eq.trans ?_ (Value.stCliqueValue K lam (listTables K W)) : _ = Paper.cliqueValue lam (listTables K W))
  unfold Net.value
  refine sum_congr rfl fun z hz => congrArg₂ (· * ·) (prod_congr rfl fun a _ => ?_) rfl
  have ha : (z a).length = (K - 1) * lam := mem_words.1 (Fintype.mem_piFinset.1 hz a)
  change W a.val (z a) = W a.val (List.ofFn fun u : Fin K => if u = a then [] else copyAt lam a u (z a)).flatten
  rw [flatten_copies a ha]
end ExplicitCost
