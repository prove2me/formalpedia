-- Prove2me | solution 1 for ExplicitCost.lists_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:24.050791+00:00
-- url     : https://prove2.me/submissions/454143a3-ad46-4485-b743-e02e4f30684a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternIs
import Definitions.Def_Printed_GroupingProcs
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentNumbers
import Theorems.Thm_ExplicitCost_card_I_pos


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    (listsAsPieces (listsOf D lam)).cnt 0 lam = (piecesOf D c).cnt 0 lam ∧ 1 ≤ (listsAsPieces (listsOf D lam)).cnt 0 lam ∧
      ∀ tr, ∀ j < (listsAsPieces (listsOf D lam)).cnt 0 lam, (listsAsPieces (listsOf D lam)).cap tr 0 lam j = (piecesOf D c).cap tr 0 lam j := by
  obtain ⟨h1, h2⟩ := hLA D c lam (hS.short lam)
  refine ⟨h1, ?_, fun tr j hj => h2 tr j ?_⟩
  · rw [h1]
    exact card_I_pos hS.is hlam
  · rw [h1] at hj
    exact hj
end ExplicitCost
