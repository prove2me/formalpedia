-- Prove2me | solution 1 for Coding.mu_pos_of_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:02:51.397852+00:00
-- url     : https://prove2.me/submissions/e14aac52-1221-49c8-b247-70c840b67b66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Coding_fst_lt_of_mem_occAll
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : 0 < mu g Φ := by
  have h1 := fst_lt_of_mem_occAll ho
  have h2 := le_mul_mu hg Φ
  rcases Nat.eq_zero_or_pos (mu g Φ) with h | h
  · rw [h, Nat.mul_zero] at h2
    omega
  · exact h
end Coding
