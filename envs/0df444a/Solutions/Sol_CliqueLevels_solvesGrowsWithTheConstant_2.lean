-- Prove2me | solution 2 for CliqueLevels.solvesGrowsWithTheConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:57.636006+00:00
-- url     : https://prove2.me/submissions/058ce082-1de2-4835-8b23-06fd8d415a4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
import Theorems.Thm_CliqueLevels_Proof_factor_mono
import Theorems.Thm_CliqueLevels_Proof_bound_mono
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CliqueLevels
open Groundwork Printed Proof
namespace CliqueLevels
theorem _root_.solution : SolvesGrowsWithTheConstant := by
  intro M K e C₀ C₁ hK h
  refine ⟨fun hS l lam B W hl hB hW => ?_, fun hS l lam B W hl hB hW => ?_⟩
  · obtain ⟨T, S, hr, hT, hSz⟩ := hS l lam B W hl hB hW
    exact ⟨T, S, hr, hT.trans (bound_mono (hK l) hl h), hSz.trans (bound_mono (hK l) hl h)⟩
  · obtain ⟨T, S, hr, hT, hSz⟩ := hS l lam B W hl hB hW
    exact ⟨T, S, hr, hT.trans (bound_mono (hK l) hl h), hSz.trans (factor_mono (hK l) hl h)⟩
end CliqueLevels
