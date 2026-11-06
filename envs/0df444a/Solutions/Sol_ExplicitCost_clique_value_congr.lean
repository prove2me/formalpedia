-- Prove2me | solution 1 for ExplicitCost.clique_value_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:11:50.123067+00:00
-- url     : https://prove2.me/submissions/a5a0bf2f-2d4e-4345-a993-4be3373ea297

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K lam : ℕ} {W W' : Fin K → List Bool → ℤ} (h : ∀ w, ∀ z ∈ words ((K - 1) * lam), W w z = W' w z) : (clique K lam W).value = (clique K lam W').value := by
  unfold Net.value
  refine Finset.sum_congr rfl fun z hz => ?_
  congr 1
  exact Finset.prod_congr rfl fun a _ => h a _ (Fintype.mem_piFinset.1 hz a)
end ExplicitCost
