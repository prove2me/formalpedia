-- Prove2me | solution 1 for Coding.capF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:26:44.930065+00:00
-- url     : https://prove2.me/submissions/699bc075-70d4-42ac-a729-b8adb1f5873f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_testsBetween_comm
import Theorems.Thm_Coding_links_eq_tests
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a b : ℕ) : capF g 3 Φ a b = (testsBetween g Φ a b).length := by
  have key : ∀ {a b : ℕ}, a ≤ b → (links g 3 Φ a b).length = (testsBetween g Φ a b).length := by
    intro a b hab
    have h := congrArg List.length (links_eq_tests hg h3 hab)
    rwa [List.length_map, List.length_map] at h
  unfold capF
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, key h]
  · rw [min_eq_right h, max_eq_left h, key h, testsBetween_comm]
end Coding
