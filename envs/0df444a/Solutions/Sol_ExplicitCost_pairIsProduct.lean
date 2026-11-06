-- Prove2me | solution 1 for ExplicitCost.pairIsProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:51.435145+00:00
-- url     : https://prove2.me/submissions/5ca7c65a-2d77-4205-b42c-0dc547be769b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
import Theorems.Thm_ExplicitCost_test_and_loop
import Theorems.Thm_ExplicitCost_pair_row
import Theorems.Thm_ExplicitCost_pair_col
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : PairIsProduct := by
  intro ρ c x₀ D hS g lam y tr W _ hlam _ a b hab z hz z' hz'
  rw [test_and_loop g tr lam ((a.val, b.val), (z, z')) fun i i' => pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri a.val b.val) (tri i i'))) (rectStrings g tr lam ((a.val, b.val), (z, z')) i i')]
  cases tr
  · exact pair_row hS hlam y _ hab (mem_words.1 hz) (mem_words.1 hz')
  · exact pair_col hS hlam y _ hab (mem_words.1 hz) (mem_words.1 hz')
end ExplicitCost
