-- Prove2me | solution 1 for CliqueLevels.solvesOfSolvesInFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:32.63326+00:00
-- url     : https://prove2.me/submissions/db92d4ff-f62b-458c-99aa-e443892b8c7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_Levels
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CliqueLevels
open QueryMachines Printed
namespace CliqueLevels
theorem _root_.solution : SolvesOfSolvesInFactor := by
  intro M K e C₀ he h l lam B W hlam hB hW
  obtain ⟨T, S, h1, h2, h3⟩ := h l lam B W hlam hB hW
  refine ⟨T, S, h1, h2, h3.trans ?_⟩
  have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ (e l * (K l : ℝ) ^ 2 * lam) := Real.one_le_rpow one_le_two (mul_nonneg (mul_nonneg (he l) (by positivity)) (by positivity))
  unfold factor bound
  exact le_mul_of_one_le_left (by positivity) h4
end CliqueLevels
