-- Prove2me | solution 1 for ExplicitCost.totalG_lists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:08.758862+00:00
-- url     : https://prove2.me/submissions/efa56d93-c056-440b-a15c-21c5b34d15dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_ExplicitCost_listsAgree
import Theorems.Thm_ExplicitCost_totalG_congr


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y : ℕ) :
    totalG (listsAsPieces (listsOf D lam)) p d tr 0 lam y = totalG (piecesOf D c) p d tr 0 lam y := by
  obtain ⟨h1, h2⟩ := listsAgree D c lam (hS.short lam)
  exact totalG_congr h1 (h1.trans_ge (card_I_pos hS.is hlam)) (fun tr j hj => h2 tr j (hj.trans_eq h1)) p d tr y
end ExplicitCost
