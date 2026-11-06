-- Prove2me | solution 1 for ExplicitCost.three_timeBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:20:17.467193+00:00
-- url     : https://prove2.me/submissions/739cbf8a-d775-4eab-b56f-ef5560952887

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
import Theorems.Thm_ExplicitCost_base_ge
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (ρ : ℝ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : 3 * timeBound ρ x₀ C l lam B ≤ timeBound ρ x₀ (C + 1) l lam B := by
  have hX := base_ge hx l hlam hB
  have hK : 1 ≤ Levels.Gen.K x₀ l ^ 2 := Nat.one_le_pow _ _ (by have := ClauseBound.Gen.Rate.big_le_K hx l; omega)
  have h3 : (3 : ℝ) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (Levels.Gen.K x₀ l ^ 2) := by
    calc (3 : ℝ) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ 1 := by rw [pow_one]; linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hK
  unfold timeBound
  rw [Nat.add_mul, Nat.one_mul, pow_add]
  have hp : 0 ≤ (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) * ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hp]
end ExplicitCost
