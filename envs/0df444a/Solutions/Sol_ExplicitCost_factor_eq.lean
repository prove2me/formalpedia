-- Prove2me | solution 1 for ExplicitCost.factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:34:59.174208+00:00
-- url     : https://prove2.me/submissions/9dd72c15-3b12-4cfe-9ef2-3c7dc894fa04

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridFf_eq
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_f
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    (patternNet D c g tr lam y W).f a b z θ = gridFf (piecesOf D c) [()] g g tr 0 lam y ((a.val, b.val), (z, θ)) :=
  (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).trans (gridFf_eq (piecesOf D c) [()] g g tr 0 lam y a b z θ).symm
end ExplicitCost
