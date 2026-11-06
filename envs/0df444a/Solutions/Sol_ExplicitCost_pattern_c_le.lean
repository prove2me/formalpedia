-- Prove2me | solution 1 for ExplicitCost.pattern_c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:05:00.814829+00:00
-- url     : https://prove2.me/submissions/218f8944-81a1-48e6-b74b-02de93fadba3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c_le
import Theorems.Thm_ExplicitCost_cutsOK_piecesOf
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (a b : Fin (nParts g g tr)) : (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by
  have h := gridN_c_le (cutsOK_piecesOf hS hlam [()]) g g tr y (fun w θ => W w.val (List.ofFn θ).flatten) a b
  rw [nMemb_self] at h
  exact h.trans (le_of_eq (by change g ^ 2 * (1 * lam) = _; rw [Nat.one_mul]))
end ExplicitCost
