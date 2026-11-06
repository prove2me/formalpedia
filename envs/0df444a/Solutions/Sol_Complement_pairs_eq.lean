-- Prove2me | solution 1 for Complement.pairs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:07:51.722021+00:00
-- url     : https://prove2.me/submissions/60dc1026-c0ba-45d5-967c-ab804b0336cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Complement_Sets
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution (n : ℕ) : pairs n = (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u.val, v.val) := by
  have hr : List.range n = (List.finRange n).map fun i : Fin n => i.val := List.map_coe_finRange_eq_range.symm
  change (List.range n).flatMap (fun a => (List.range n).map (Prod.mk a)) = _
  rw [hr, List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  rfl
end Complement
