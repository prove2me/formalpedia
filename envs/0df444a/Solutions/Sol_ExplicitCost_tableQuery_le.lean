-- Prove2me | solution 1 for ExplicitCost.tableQuery_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:11.370484+00:00
-- url     : https://prove2.me/submissions/de83d961-f0b0-43fb-a2e0-e1ba7f92c487

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
theorem _root_.solution {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C : ℕ} (hC : 1 ≤ C) :
    ((Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3 + 4 : ℕ) : ℝ) ≤ sizeBound x₀ C l lam B := by
  have hX := base_ge hx l hlam hB
  have hK : (8 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 8 ≤ Levels.Gen.K x₀ l)
  have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h2 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h3 : 2 ≤ C * Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    nlinarith
  unfold sizeBound
  refine le_trans ?_ (pow_le_pow_right₀ (by linarith) h3)
  push_cast
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) - 8) (by linarith : (0 : ℝ) ≤ (lam : ℝ) + B - 2), mul_self_nonneg ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B) - 8), mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ)) (by linarith : (0 : ℝ) ≤ (B : ℝ) - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ)) (by linarith : (0 : ℝ) ≤ (lam : ℝ) - 1)]
end ExplicitCost
