-- Prove2me | solution 1 for ExplicitCost.callNet_total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:55.197042+00:00
-- url     : https://prove2.me/submissions/d876a5fa-6641-410a-a89c-25e051c61cc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChildIsGood
import Theorems.Thm_ExplicitCost_level_numbers
import Theorems.Thm_ExplicitCost_total_direction
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hT : TotalsAre) (hSm : SmallerTotal) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {a : Ctx} (f : TableQuery → Option Ans) {l y : ℕ} (hl : cLev a = l + 1) (hlam : 1 ≤ cLam a)
    (hy : y < #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l)) :
    ((callNet D c x₀ l a f y).U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * cLam a * (ρ + 1 / Levels.Gen.g x₀ l) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) := by
  have hg2 := (level_numbers hS.x₀_ge l).2.2
  have e : (callNet D c x₀ l a f y).U = min (totalG (listsAsPieces (listsOf D (cLam a))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (cLam a) y)
      (totalG (listsAsPieces (listsOf D (cLam a))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (cLam a) y) :=
    (hT ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hlam).trans (total_direction D x₀ a.1 hl y)
  rw [e]
  exact hSm ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) y hg2 hlam hy
end ExplicitCost
