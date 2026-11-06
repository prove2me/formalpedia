-- Prove2me | solution 1 for ExplicitCost.abs_factorItem_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:17.894536+00:00
-- url     : https://prove2.me/submissions/1cc789ae-c933-4cdf-9743-609f397b93ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_ExplicitCost_length_factorChunk
import Theorems.Thm_ExplicitCost_dig_mem
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_SingleBitPieces_Level_Presents_size_f
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (hg : 0 < g) {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) (j : ℕ) : |factorItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by
  unfold factorItem
  split_ifs with hlt
  · exact hS.is.size_f lam hlam _ (dig_mem hS hlam g tr y _ _) _ _ _ _ (mem_words.2 (length_factorChunk hθ hlt hg))
  · rw [abs_one]
    exact one_lt_pow₀ (by norm_num) (by positivity)
end ExplicitCost
