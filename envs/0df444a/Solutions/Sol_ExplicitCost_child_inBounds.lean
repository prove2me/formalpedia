-- Prove2me | solution 1 for ExplicitCost.child_inBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:27.646955+00:00
-- url     : https://prove2.me/submissions/1989d3c5-1a9a-4110-be96-e6fc1a2431d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
import Theorems.Thm_ExplicitCost_lamAt_step
import Theorems.Thm_ExplicitCost_bitsAt_step
import Theorems.Thm_ExplicitCost_bitsOne_mono
import Theorems.Thm_ExplicitCost_bitsOut_mono
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution {a a' : Ctx} (hρ : 1 / 2 ≤ ρ) (hIn : InBounds ρ c x₀ l lam B a) (h1 : 1 ≤ cLam a) (hj : cLev a = j + 1) (hj' : cLev a' = j)
    (hL : (Levels.Gen.K x₀ j : ℝ) ^ 2 * cLam a' ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * cLam a) + (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) + (Levels.Gen.K x₀ j : ℝ) ^ 2)
    (hB : cB a' = bitsOut (Levels.Gen.K x₀ j) (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ j) (cLam a) (cB a))) : InBounds ρ c x₀ l lam B a' := by
  obtain ⟨i1, i2, i3⟩ := hIn
  rw [hj] at i1 i2 i3
  have hjl : j < l := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hj', lamAt_step ρ c x₀ lam B hjl]
    have hK : (0 : ℝ) < (Levels.Gen.K x₀ j : ℝ) ^ 2 := by
      have := K_pos x₀ j
      positivity
    refine Nat.le_floor ((le_div_iff₀ hK).2 ?_)
    have hz : (0 : ℝ) ≤ Levels.Gen.zeta j := by unfold Levels.Gen.zeta; positivity
    have c1 : (cLam a : ℝ) ≤ lamAt ρ c x₀ l lam B (j + 1) := by exact_mod_cast i2
    have c0 : (1 : ℝ) ≤ cLam a := by exact_mod_cast h1
    have hlog : Real.logb 2 (2 * cLam a) ≤ Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have m1 : (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * cLam a) ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 (by positivity)) (by linarith)
    have m2 : (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) ≤ (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) := mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  · rw [hj', hB, bitsAt_step ρ c x₀ lam B hjl]
    exact bitsOut_mono _ _ (Nat.mul_le_mul_left _ i2) (bitsOne_mono _ _ i2 i3)
end ExplicitCost
