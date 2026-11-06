-- Prove2me | solution 1 for FixedWidthSteps.smallCasesAreWithinTheBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:01.338952+00:00
-- url     : https://prove2.me/submissions/c659d63f-8e47-479b-8eeb-fd2922ec41af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small
import Theorems.Thm_FixedWidthSteps_timeVariables_mono
import Theorems.Thm_FixedWidthSteps_exists_le_timeVariables
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution : SmallCasesAreWithinTheBound := by
  intro α c k n₀ _
  induction n₀ with
  | zero => exact ⟨0, fun n _ h => absurd h (Nat.not_lt_zero n)⟩
  | succ m ih =>
    obtain ⟨C, hC⟩ := ih
    by_cases hm : 4 ≤ m
    · obtain ⟨C', hC'⟩ := exists_le_timeVariables α hm (2 ^ (c * m) * m ^ (c * k))
      refine ⟨max C C', fun n h4 hlt => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | rfl
      · exact (hC n h4 h).trans (timeVariables_mono α h4 (le_max_left _ _))
      · exact hC'.trans (timeVariables_mono α h4 (le_max_right _ _))
    · exact ⟨C, fun n h4 hlt => hC n h4 (by omega)⟩
end FixedWidthSteps
