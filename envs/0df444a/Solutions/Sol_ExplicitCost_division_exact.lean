-- Prove2me | solution 1 for ExplicitCost.division_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:21.049267+00:00
-- url     : https://prove2.me/submissions/018da61f-3609-4b9f-92e2-f6bd7bcea1b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ExplicitCost_K_succ_mul
import Theorems.Thm_ExplicitCost_nPatterns_ready
import Theorems.Thm_ExplicitCost_rG_ready
import Theorems.Thm_ExplicitCost_two_le_K


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (hExp : Expansion) (hS : Setting ρ c x₀ D) (Bound : Ctx → Prop) (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    (spec D c x₀ Bound).val a f = Sum.inl ((∑ y ∈ range (nPatterns (readyOf D x₀ a.1)), (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) / (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ)) := by
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hE := hExp ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) (readTables f) (fun y => direction (readyOf D x₀ a.1, y)) (by omega) hF.1
  have hnP : nPatterns (readyOf D x₀ a.1) = #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := nPatterns_ready D x₀ a.1 hl
  have hdpos := hS.is.d_pos _ hF.1
  have hd : (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ) = (D.fam (cLam a)).d ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
    have h1 : rD (readyOf D x₀ a.1) = (D.fam (cLam a)).d := rfl
    have h2 : rRect (readyOf D x₀ a.1) = nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
      unfold rRect
      rw [rG_ready D x₀ a.1 hl]
    rw [h1, h2]
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
  rw [hnP, ← hE, hd, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by omega))]
  show Sum.inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables f w.val).value = _
  rw [hl, K_succ_mul]
end ExplicitCost
