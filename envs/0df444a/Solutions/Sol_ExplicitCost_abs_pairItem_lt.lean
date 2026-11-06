-- Prove2me | solution 1 for ExplicitCost.abs_pairItem_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:45:08.810447+00:00
-- url     : https://prove2.me/submissions/ccdcf928-853b-4f52-8de3-cbbe2182d18a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_ExplicitCost_dig_mem


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (q : PsiQ) (j : ℕ) : |pairItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by
  unfold pairItem
  split_ifs
  · exact hS.is.size_A lam hlam _ (dig_mem hS hlam g tr y _ _) _ _ _ _
  · rw [abs_one]
    exact one_lt_pow₀ (by norm_num) (by positivity)
end ExplicitCost
