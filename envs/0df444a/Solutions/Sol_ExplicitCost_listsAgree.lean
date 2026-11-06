-- Prove2me | solution 1 for ExplicitCost.listsAgree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:19.86337+00:00
-- url     : https://prove2.me/submissions/69dc647b-1361-4544-8985-aa8cf6f5f62d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_getD_map_of_lt
import Theorems.Thm_ExplicitCost_length_sortI
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : ListsAgree := by
  intro D c lam hshort
  refine ⟨length_sortI D lam, fun tr j hj => ?_⟩
  have hj' : j < ((D.fam lam).I.sort).length := by rw [length_sortI]; exact hj
  change min ((if tr = true then (listsOf D lam).2.2 else (listsOf D lam).2.1).getD j 0) (2 * lam) = D.cap lam tr (indexAt D lam j)
  have e : (if tr = true then (listsOf D lam).2.2 else (listsOf D lam).2.1).getD j 0 = D.cap lam tr (indexAt D lam j) := by
    cases tr
    · exact getD_map_of_lt (fun i => D.cap lam false i) _ hj' 0 0
    · exact getD_map_of_lt (fun i => D.cap lam true i) _ hj' 0 0
  rw [e]
  exact min_eq_left (hshort tr _)
end ExplicitCost
