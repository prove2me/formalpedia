-- Prove2me | solution 1 for ExplicitCost.label_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:03.016435+00:00
-- url     : https://prove2.me/submissions/b16de551-7436-4595-86c7-4ca227984b78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
import Theorems.Thm_ExplicitCost_zeta_cast
import Theorems.Thm_ClauseBound_Gen_K_cast
import Theorems.Thm_ClauseBound_Gen_zeta_pos
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l lam U : ℕ) :
    (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
      U + 2 * Levels.Gen.zeta l * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) + (Levels.Gen.K x₀ l : ℝ) ^ 2 := by
  have hK : (0 : ℝ) < Levels.Gen.K x₀ l := by rw [ClauseBound.Gen.K_cast]; positivity
  have hz := ClauseBound.Gen.zeta_pos l
  unfold AppRunningTime.Lof
  rw [zeta_cast]
  have ht : 0 ≤ ((U : ℝ) + 2 * Levels.Gen.zeta l * Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * lam : ℕ) : ℝ)) / (Levels.Gen.K x₀ l : ℝ) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ht).le (by positivity : 0 ≤ (Levels.Gen.K x₀ l : ℝ) ^ 2)
  refine h1.trans (le_of_eq ?_)
  push_cast
  field_simp
end ExplicitCost
