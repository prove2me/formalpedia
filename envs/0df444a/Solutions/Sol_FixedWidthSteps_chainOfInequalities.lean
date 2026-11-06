-- Prove2me | solution 1 for FixedWidthSteps.chainOfInequalities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:48.028899+00:00
-- url     : https://prove2.me/submissions/c18cc06f-c449-46ca-aa35-e2bc0edcb8be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Between
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_FixedWidthSteps_Numbers
import Theorems.Thm_GeneralPieces_Asymptotic_between
import Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_logK
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a


set_option autoImplicit false
section
section
open FixedWidthSteps
open Groundwork PaddedDescent.F Levels.Gen MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution : ChainOfInequalities := by
  intro ρ x₀ l hρ hρ1 hx
  have hA := GeneralPieces.PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hlog : (2 : ℝ) ^ (l + 1) ≤ lg (K x₀ l) := GeneralPieces.PartAUse.two_pow_le_logK hA (by omega) l
  refine ⟨(hA.e_bounds l).1, ?_, one_div_le_one_div_of_le (by positivity) hlog, fun r h1 h2 => GeneralPieces.Asymptotic.between ρ x₀ l r hρ hx h1 h2⟩
  have h : (1 / 2 : ℝ) ^ l ≤ ρ ^ l := pow_le_pow_left₀ (by norm_num) hρ l
  have e : 1 / (2 : ℝ) ^ (l + 1) = 1 / 2 * (1 / 2) ^ l := by rw [pow_succ, one_div_pow]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by norm_num)
end FixedWidthSteps
