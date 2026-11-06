-- Prove2me | solution 1 for ExplicitCost.pattern_is
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:16.066979+00:00
-- url     : https://prove2.me/submissions/d9017968-050e-4926-88e2-82c6eeb677ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_ExplicitCost_sized_zero
import Theorems.Thm_ExplicitCost_abs_factor_lt
import Theorems.Thm_ExplicitCost_pair_fact
import Theorems.Thm_ExplicitCost_abs_pair_lt
import Theorems.Thm_ExplicitCost_abs_weight_lt
import Theorems.Thm_ExplicitCost_c_eq
import Theorems.Thm_ExplicitCost_mem_S_iff
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) :
    (patternNet D c g tr lam y W).Is (g ^ 3 * lam) (bitsOne c g lam B) where
  P_pos := Nat.mul_pos (by positivity) hlam
  B_pos := by
    unfold bitsOne
    have : 1 ≤ g * B := Nat.mul_pos hg hB
    omega
  len_S a z hz := by
    rw [(mem_S_iff a z).1 hz, nMemb_self]
    change _ = g ^ 3 * lam
    ring
  len_le _ := le_rfl
  Ψ_symm a b _ z _ z' _ := Network.Ψ_comm (gridOf D c g tr lam y W) b a z' z
  c_symm a b := (sized_zero (y := y) hS hlam).c_symm a b
  fact a b hab z _ z' _ := pair_fact hab z z'
  i a := by
    refine ((sized_zero (y := y) hS hlam).sum_c a).trans (le_of_eq ?_)
    rw [nMemb_self, nParts_self]
    ring
  ii_W a z hz := abs_weight_lt hg hlam hW a ((mem_S_iff a z).1 hz)
  ii_Ψ a b hab z hz z' hz' := abs_pair_lt hS hg hlam hB hab ((mem_S_iff a z).1 hz) ((mem_S_iff b z').1 hz')
  ii_f a b hab z hz θ hθ := abs_factor_lt hS hg hlam hB hab ((mem_S_iff a z).1 hz) ((mem_words.1 hθ).trans (c_eq hab))
end ExplicitCost
