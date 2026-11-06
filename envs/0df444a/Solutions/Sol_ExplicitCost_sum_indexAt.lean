-- Prove2me | solution 1 for ExplicitCost.sum_indexAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:18:27.640196+00:00
-- url     : https://prove2.me/submissions/a1376b3a-86ef-45d6-ac3b-dc70b7925ee2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_length_sortI
import Theorems.Thm_ExplicitCost_sum_range_getD

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (lam : ℕ) (f : ℤ → ℤ) : ∑ j ∈ range #(D.fam lam).I, f (indexAt D lam j) = ∑ i ∈ (D.fam lam).I, f i := by
  rw [← length_sortI]
  unfold indexAt
  rw [sum_range_getD, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
end ExplicitCost
