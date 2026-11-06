-- Prove2me | solution 1 for ExplicitCost.capG_ofLists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:50.648507+00:00
-- url     : https://prove2.me/submissions/2b9bc2cc-9e8e-4ff1-b9fb-973e7bc910dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternIs
import Definitions.Def_Printed_GroupingProcs
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentNumbers
import Theorems.Thm_ExplicitCost_lists_agree
import Theorems.Thm_ExplicitCost_capG_congr


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y a b : ℕ) : capG (listsAsPieces (listsOf D lam)) p d tr 0 lam y a b = capG (piecesOf D c) p d tr 0 lam y a b :=
  capG_congr (lists_agree hLA hS hlam).1 (lists_agree hLA hS hlam).2.1 (lists_agree hLA hS hlam).2.2 p d tr y a b
end ExplicitCost
