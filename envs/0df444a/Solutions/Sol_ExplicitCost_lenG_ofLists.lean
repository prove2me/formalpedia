-- Prove2me | solution 1 for ExplicitCost.lenG_ofLists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:09:03.137601+00:00
-- url     : https://prove2.me/submissions/ceb364e3-de42-4495-820c-9ff4ad7bc730

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternIs
import Definitions.Def_Printed_GroupingProcs
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentNumbers
import Theorems.Thm_ExplicitCost_lists_agree
import Theorems.Thm_ExplicitCost_lenG_congr


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (d : ℕ) (tr : Bool) (y q κ : ℕ) : lenG (listsAsPieces (listsOf D lam)) d tr 0 lam y q κ = lenG (piecesOf D c) d tr 0 lam y q κ :=
  lenG_congr (lists_agree hLA hS hlam).1 (lists_agree hLA hS hlam).2.1 (lists_agree hLA hS hlam).2.2 d tr y q κ
end ExplicitCost
