-- Prove2me | solution 1 for ExplicitCost.total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:40.462464+00:00
-- url     : https://prove2.me/submissions/09a7ed04-9dd3-43a3-9b81-c9c7b4b1d810

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LabelCrude
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_shared_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) :
    (patternNet D c g tr lam y W).U ≤ g ^ 4 * lam := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, (patternNet D c g tr lam y W).c a b ≤ ∑ a : Fin (nParts g g tr), ∑ _b ∈ univ.erase a, g ^ 2 * lam :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => shared_le hS g hlam y tr W a b
    _ ≤ ∑ _a : Fin (nParts g g tr), g * (g ^ 2 * lam) := Finset.sum_le_sum fun a _ => by
        rw [Finset.sum_const, smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans (le_of_eq ?_))
        rw [Finset.card_univ, Fintype.card_fin, nParts_self]
    _ = g ^ 4 * lam := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, nParts_self]
        ring
end ExplicitCost
