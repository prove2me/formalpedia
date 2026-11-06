-- Prove2me | solution 1 for ExplicitCost.label_le_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:25.231214+00:00
-- url     : https://prove2.me/submissions/aaba201a-9ada-4ea1-8eac-8fd5bc83d974

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LabelCrude
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ExplicitCost_label_first


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l lam U : ℕ) (hx : 18 ≤ x₀) (hU : U ≤ Levels.Gen.g x₀ l ^ 4 * lam) :
    AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 := by
  have hK : (2 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 2 ≤ Levels.Gen.K x₀ l)
  have hK2 : (2 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) ^ 2 := by nlinarith
  have hz : Levels.Gen.zeta l ≤ 1 / 2 := by
    unfold Levels.Gen.zeta
    have h2 : (2 : ℝ) ≤ 2 ^ (l + 5) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
        _ ≤ 2 ^ (l + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hUr : (U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by exact_mod_cast hU
  have hN : (0 : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by positivity
  have h1 := label_first x₀ l lam U
  have h2 : 2 * Levels.Gen.zeta l * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by nlinarith
  have h3 : (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
      (Levels.Gen.K x₀ l : ℝ) ^ 2 * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam + 1) := by nlinarith
  have h4 := le_of_mul_le_mul_left h3 (by linarith)
  exact_mod_cast h4
end ExplicitCost
