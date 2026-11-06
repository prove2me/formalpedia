-- Prove2me | solution 1 for ExplicitCost.abs_factor_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:52.055696+00:00
-- url     : https://prove2.me/submissions/9672bcbe-868c-4922-8142-64735380f5d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ExplicitCost_sized_zero
import Theorems.Thm_ExplicitCost_pow_lt_bitsOne
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_f
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) : |(patternNet D c g tr lam y W).f a b z θ| < 2 ^ bitsOne c g lam B := by
  have e : (patternNet D c g tr lam y W).f a b z θ = (gridN (piecesOf D c) [()] g g tr 0 lam y fun _ _ => 0).f a b z θ :=
    (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).trans (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).symm
  rw [e]
  exact ((sized_zero hS hlam).abs_f a b z θ).trans_lt (pow_lt_bitsOne hg hB)
end ExplicitCost
