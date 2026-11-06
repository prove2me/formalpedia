-- Prove2me | solution 1 for ExplicitCost.pair_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:57.045206+00:00
-- url     : https://prove2.me/submissions/464d26fc-850b-47d4-801d-25473737d3d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hPP : PairIsProduct) {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    (patternNet D c g tr lam y W).Ψ a b z z' = if straightOK g tr lam (ordered ((a.val, b.val), (z, z'))) = true then
      ∏ j ∈ range (g * g), (if j / g < j % g then
        pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri (ordered ((a.val, b.val), (z, z'))).1.1 (ordered ((a.val, b.val), (z, z'))).1.2) (tri (j / g) (j % g))))
          (rectStrings g tr lam (ordered ((a.val, b.val), (z, z'))) (j / g) (j % g)) else 1)
    else 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · have e : ordered ((a.val, b.val), (z, z')) = ((a.val, b.val), (z, z')) := if_pos (Fin.lt_def.1 h)
    rw [e]
    exact hPP ρ c x₀ D hS g lam y tr W hg hlam hy a b h z hz z' hz'
  · have e : ordered ((a.val, b.val), (z, z')) = ((b.val, a.val), (z', z)) := if_neg (not_lt.2 (Fin.lt_def.1 h).le)
    rw [e]
    refine Eq.trans ?_ (hPP ρ c x₀ D hS g lam y tr W hg hlam hy b a h z' hz' z hz)
    exact Network.Ψ_comm (gridOf D c g tr lam y W) a b z z'
end ExplicitCost
