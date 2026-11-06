-- Prove2me | solution 1 for ExplicitCost.child_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:40:31.319201+00:00
-- url     : https://prove2.me/submissions/1303147f-9c8c-480d-96ec-16aa13c0f6ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_parentAt_readyOf
import Theorems.Thm_ExplicitCost_pattern_input
import Theorems.Thm_ExplicitCost_unary_length_eq
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hy : y < nPatterns (readyOf D x₀ a.1)) (x : ℕ) :
    child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)) =
      ((unary l, unary (labelLength (searchInput c (readyOf D x₀ a.1, y))), unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))), some (mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x)) := by
  obtain ⟨-, hsi, -, -⟩ := pattern_input hLL hBN hS hF hl hy
  have h1 : inK (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l := by rw [hsi]; exact length_unary _
  have h2 : inG (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.g x₀ l := by rw [hsi]; exact (length_unary _).trans (nParts_self _ _)
  have h3 : inP (searchInput c (readyOf D x₀ a.1, y)) = (Levels.Gen.g x₀ l ^ 3 * cLam a) := by rw [hsi]; exact length_unary _
  have h4 : inB (searchInput c (readyOf D x₀ a.1, y)) = (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by rw [hsi]; exact length_unary _
  have ht : a.1.1.tail = unary l := by
    rw [← unary_length_eq a.1.1.tail, List.length_tail]
    show unary (cLev a - 1) = _
    rw [hl]
    rfl
  refine Prod.ext (Prod.ext ht (Prod.ext rfl ?_)) (congrArg some (parentAt_readyOf D x₀ a.1 hl y x))
  show unary (bitsOut (inK (searchInput c (readyOf D x₀ a.1, y))) (inG (searchInput c (readyOf D x₀ a.1, y))) (inP (searchInput c (readyOf D x₀ a.1, y))) (inB (searchInput c (readyOf D x₀ a.1, y)))) = _
  rw [h1, h2, h3, h4]
end ExplicitCost
