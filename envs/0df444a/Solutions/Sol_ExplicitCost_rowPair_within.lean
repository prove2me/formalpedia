-- Prove2me | solution 1 for ExplicitCost.rowPair_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:16.3097+00:00
-- url     : https://prove2.me/submissions/44fc74d2-02e3-4532-8346-cb7303952cc0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_ExplicitCost_size_ordered
import Theorems.Thm_ExplicitCost_rowPair_eq
import Theorems.Thm_ExplicitCost_pairLoop_within
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_mem_S_iff
import Theorems.Thm_ExplicitCost_pair_eq


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hPP : PairIsProduct) (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool} (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    rowPair.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, z'))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, z'))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).Ψ a b z z') := by
  rw [pair_eq hPP hS hg hlam hy hab hz hz', rowPair_eq]
  have hl := (mem_S_iff a z).1 hz
  have hl' := (mem_S_iff b z').1 hz'
  have hs : size (p, ordered ((a.val, b.val), (z, z'))) = size (p, ((a.val, b.val), (z, z'))) := congrArg (size p + ·) (size_ordered _)
  rw [← hs]
  refine mapIn_within (pairLoop_within hLA hG hL hT hY hLs hS (by omega) hlam hLam ?_ ?_ ?_ ?_)
  all_goals
    unfold ordered
    split_ifs
    all_goals first | exact a.2 | exact b.2 | exact hl | exact hl'
end ExplicitCost
