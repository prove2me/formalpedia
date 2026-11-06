-- Prove2me | solution 1 for ExplicitCost.abs_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:58.056483+00:00
-- url     : https://prove2.me/submissions/2eb4978d-6ac0-4f4f-9ff2-15f65fa774b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_ExplicitCost_pointQuery_ok
import Theorems.Thm_ExplicitCost_weight_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) (a : Fin (nParts g g tr)) {z : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) : |(patternNet D c g tr lam y W).W a z| < 2 ^ bitsOne c g lam B := by
  have h1 : |(patternNet D c g tr lam y W).W a z| ≤ (2 ^ B) ^ g := by
    rw [weight_eq a hz]
    split_ifs
    · rw [Finset.abs_prod]
      refine (Finset.prod_le_prod (g := fun _ => (2 : ℤ) ^ B) (fun i _ => abs_nonneg _) fun i hi => ?_).trans (le_of_eq ?_)
      · obtain ⟨q1, q2⟩ := pointQuery_ok a hz (Finset.mem_range.1 hi)
        exact (hW _ q1 _ (mem_words.2 q2)).le
      · rw [Finset.prod_const, Finset.card_range, nMemb_self]
    · rw [abs_zero]
      positivity
  refine h1.trans_lt ?_
  rw [← pow_mul]
  refine pow_lt_pow_right₀ (by norm_num) ?_
  unfold bitsOne
  have : 1 ≤ g ^ 2 * (2 * lam) ^ c := Nat.mul_pos (by positivity) (by positivity)
  rw [Nat.mul_comm B g]
  omega
end ExplicitCost
