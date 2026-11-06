-- Prove2me | solution 1 for Coding.map_links
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:26:51.03378+00:00
-- url     : https://prove2.me/submissions/a267a797-525f-4389-8731-98ee658fb883

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_links_eq_tests
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) {β : Type} (F : ℕ × ℕ → β) :
    (links g 3 Φ a b).map (fun p => F (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => F (place p.1, place p.2) := by
  have h := congrArg (List.map F) (links_eq_tests hg h3 hab)
  rw [List.map_map, List.map_map] at h
  exact h
end Coding
