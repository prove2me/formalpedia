-- Prove2me | solution 1 for ExplicitCost.indexAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:27:09.707959+00:00
-- url     : https://prove2.me/submissions/f668e179-0d1c-4ede-811e-5659a9afb4e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_length_sortI
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (lam : ℕ) {j : ℕ} (hj : j < #(D.fam lam).I) : indexAt D lam j ∈ (D.fam lam).I := by
  have hj' : j < ((D.fam lam).I.sort).length := by rw [length_sortI]; exact hj
  unfold indexAt
  rw [List.getD_eq_getElem _ _ hj']
  exact (Finset.mem_sort _).1 (List.getElem_mem hj')
end ExplicitCost
