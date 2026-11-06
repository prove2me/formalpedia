-- Prove2me | solution 1 for Coding.mem_occOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:21.429516+00:00
-- url     : https://prove2.me/submissions/7934afc8-c213-4c10-9dba-60023898684c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_mu_pos_of_occ
import Theorems.Thm_Coding_div_eq_iff_block
import Theorems.Thm_Coding_mem_occAll
import Theorems.Thm_Coding_mem_occIn
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) {o : ℕ × ℕ} {a : ℕ} : o ∈ occOf g Φ a ↔ o ∈ occAll Φ ∧ clusterOf g Φ o = a := by
  rw [occOf, mem_occIn, mem_occAll, clusterOf]
  constructor
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h4, (div_eq_iff_block (by omega)).2 ⟨h1, h2⟩⟩
  · rintro ⟨h4, hc⟩
    obtain ⟨h1, h2⟩ := (div_eq_iff_block (mu_pos_of_occ hg (mem_occAll.2 h4))).1 hc
    exact ⟨h1, h2, h4⟩
end Coding
