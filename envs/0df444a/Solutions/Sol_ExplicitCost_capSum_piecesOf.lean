-- Prove2me | solution 1 for ExplicitCost.capSum_piecesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:50.1711+00:00
-- url     : https://prove2.me/submissions/7705b83a-b652-412c-901a-2ca275fafedf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_ExplicitCost_indexAt_mem


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (h : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) : (capSum (piecesOf D c) h lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := by
  have hne : (range ((piecesOf D c).cnt h lam)).Nonempty := Finset.nonempty_range_iff.2 (Nat.pos_iff_ne_zero.1 (card_I_pos hS.is hlam))
  obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup _ hne fun i => (piecesOf D c).cap false h lam i + (piecesOf D c).cap true h lam i
  unfold capSum
  rw [e]
  exact hS.is.caps lam hlam _ (indexAt_mem D lam (Finset.mem_range.1 hj))
end ExplicitCost
