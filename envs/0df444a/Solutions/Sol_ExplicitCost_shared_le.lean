-- Prove2me | solution 1 for ExplicitCost.shared_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:49.270136+00:00
-- url     : https://prove2.me/submissions/31485345-7be9-4048-bfd3-506d1d8f31ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c_le
import Theorems.Thm_ExplicitCost_cutsOK_piecesOf
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) (a b : Fin (nParts g g tr)) :
    (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by
  have h := gridN_c_le (cutsOK_piecesOf hS hlam [()]) g g tr y (fun w θ => W w.val (List.ofFn θ).flatten) a b
  rw [nMemb_self] at h
  exact h.trans (le_of_eq (congrArg _ (Nat.one_mul lam)))
end ExplicitCost
