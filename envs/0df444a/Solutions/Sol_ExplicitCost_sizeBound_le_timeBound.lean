-- Prove2me | solution 1 for ExplicitCost.sizeBound_le_timeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:20:22.431694+00:00
-- url     : https://prove2.me/submissions/1d4d2532-eb0d-4816-a85e-d6a8bf05ee11

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
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : sizeBound x₀ C l lam B ≤ timeBound ρ x₀ C l lam B := by
  have hX := base_ge hx l hlam hB
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have he : 0 ≤ Levels.Gen.e ρ x₀ l := le_trans (by positivity) (GeneralPieces.PartA.e_ge_half_pow ρ x₀ l hρ)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) := Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l ^ 2) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _))
  unfold sizeBound timeBound
  exact h2.trans (le_mul_of_one_le_left (by positivity) h1)
end ExplicitCost
