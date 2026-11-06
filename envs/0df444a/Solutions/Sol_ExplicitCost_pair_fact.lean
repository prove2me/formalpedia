-- Prove2me | solution 1 for ExplicitCost.pair_fact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:38.110785+00:00
-- url     : https://prove2.me/submissions/66afde9e-7bcc-4c5c-9e6d-848465e2292f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_lab
import Theorems.Thm_ExplicitCost_c_eq


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {a b : Fin (nParts g g tr)} (hab : a ≠ b) (z z' : List Bool) :
    (patternNet D c g tr lam y W).Ψ a b z z' = ∑ θ ∈ words ((patternNet D c g tr lam y W).c a b), (patternNet D c g tr lam y W).f a b z θ * (patternNet D c g tr lam y W).f b a z' θ := by
  change (gridOf D c g tr lam y W).Ψ a b z z' = _
  unfold Network.Ψ
  rw [gridN_lab _ _ _ _ _ _ _ _ _ hab, c_eq hab]
  rfl
end ExplicitCost
