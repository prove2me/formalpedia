-- Prove2me | solution 1 for FixedWidthSteps.timeVariablesAAlpha_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:21:18.8552+00:00
-- url     : https://prove2.me/submissions/ff74eaea-c3c5-435a-a74c-f62a223feec3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Absorb
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_FixedWidthSteps_Choice
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth Wrap
namespace FixedWidthSteps
theorem _root_.solution (C w n : ℕ) (α : ℝ) : (timeVariablesAAlpha C w n α : ℝ) ≤ (2 : ℝ) ^ (((C * w ^ 2 : ℕ) : ℝ) * expVariables α n) := by
  refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
  congr 1
  unfold expVariables
  push_cast
  ring
end FixedWidthSteps
