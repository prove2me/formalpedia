-- Prove2me | solution 1 for ExplicitCost.foldl_append_toNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:48:28.761489+00:00
-- url     : https://prove2.me/submissions/9c5f260b-ac28-45c8-b6c1-c350fc335e0d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
namespace ExplicitCost
theorem _root_.solution (v : ℕ → ℤ) (k : ℕ) : (List.range k).foldl (fun (acc : List ℕ) y => acc ++ [(v y).toNat]) [] = (List.range k).map fun y => (v y).toNat := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, List.map_append]; rfl
end ExplicitCost
