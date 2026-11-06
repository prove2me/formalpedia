-- Prove2me | solution 1 for FixedWidthSteps.rateOfThePairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:59.642693+00:00
-- url     : https://prove2.me/submissions/49dde816-3108-4d5b-9e2c-65e8af2b340c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Between
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_FixedWidthSteps_Numbers
import Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_logK
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open FixedWidthSteps
open Groundwork PaddedDescent.F Levels.Gen MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution : RateOfThePairs := by
  intro ρ x₀ l hρ hρ1 hx
  have hA := GeneralPieces.PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hlog : (2 : ℝ) ^ (l + 1) ≤ Real.logb 2 (K x₀ l) := GeneralPieces.PartAUse.two_pow_le_logK hA (by omega) l
  have hL : 0 < Real.logb 2 (K x₀ l) := lt_of_lt_of_le (by positivity) hlog
  have hρ0 : 0 < ρ := by linarith
  have hα1 : Real.logb 2 (1 / ρ) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]; linarith
  have ha : (1 : ℝ) ≤ 3 * x₀ + 6 := by have : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _; linarith
  have h0 : 0 ≤ ρ ^ l := by positivity
  have h1 : e ρ x₀ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ) := by
    have := (hA.e_bounds l).2; have := hA.rho_pow l; linarith
  have h2 : (3 * (x₀ : ℝ) + 6) ^ Real.logb 2 (1 / ρ) ≤ 3 * x₀ + 6 := by
    have := Real.rpow_le_rpow_of_exponent_le ha hα1
    rwa [Real.rpow_one] at this
  rw [Real.div_rpow (by linarith) hL.le] at h1
  have h3 : 0 < Real.logb 2 (K x₀ l) ^ Real.logb 2 (1 / ρ) := Real.rpow_pos_of_pos hL _
  show e ρ x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.logb 2 (K x₀ l) ^ Real.logb 2 (1 / ρ)
  push_cast
  exact h1.trans (div_le_div_of_nonneg_right h2 h3.le)
end FixedWidthSteps
