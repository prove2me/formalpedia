-- Prove2me | solution 1 for ExplicitCost.abs_pair_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:53.548833+00:00
-- url     : https://prove2.me/submissions/b1dcd5ee-0169-4680-afbe-108cd3bd307e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ExplicitCost_sized_zero
import Theorems.Thm_ExplicitCost_pow_lt_bitsOne
import Theorems.Thm_ExplicitCost_pair_fact
import Theorems.Thm_ExplicitCost_c_eq
import Theorems.Thm_ExplicitCost_factor_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) : |(patternNet D c g tr lam y W).Ψ a b z z'| < 2 ^ bitsOne c g lam B := by
  have e : (patternNet D c g tr lam y W).Ψ a b z z' = (patternNet D c g tr lam y fun _ _ => 0).Ψ a b z z' := by
    rw [pair_fact hab, pair_fact hab, c_eq hab, c_eq hab]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    have hθ' : θ.length = capG (piecesOf D c) g g tr 0 lam y b a := by
      rw [mem_words.1 hθ]
      unfold capG
      rw [min_comm, max_comm]
    rw [factor_eq hab hz (mem_words.1 hθ), factor_eq hab.symm hz' hθ', factor_eq hab hz (mem_words.1 hθ), factor_eq hab.symm hz' hθ']
  rw [e]
  exact ((sized_zero hS hlam).abs_Ψ a b z z' hab).trans_lt (pow_lt_bitsOne hg hB)
end ExplicitCost
