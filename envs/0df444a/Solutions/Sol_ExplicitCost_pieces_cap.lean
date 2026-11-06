-- Prove2me | solution 1 for ExplicitCost.pieces_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:00.812906+00:00
-- url     : https://prove2.me/submissions/bbf05d69-1bef-43dc-98d4-189adab09d09

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
import Theorems.Thm_ExplicitCost_getD_map_of_lt
import Theorems.Thm_ExplicitCost_indexAt_mem
import Theorems.Thm_ExplicitCost_length_sortI
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (lam : ℕ) (tr : Bool) {j : ℕ} (hj : j < ((D.fam lam).I.sort).length) :
    D.answer lam (.inr (.inr (.inl (tr, ((D.fam lam).I.sort).getD j 0)))) = some (.inl (((((D.fam lam).I.sort).map fun i => D.cap lam tr i).getD j 0 : ℕ) : ℤ)) := by
  have h1 : ((D.fam lam).I.sort).getD j 0 ∈ (D.fam lam).I := indexAt_mem D lam (by rwa [length_sortI] at hj)
  rw [getD_map_of_lt (fun i => D.cap lam tr i) _ hj 0 0]
  exact if_pos h1
end ExplicitCost
