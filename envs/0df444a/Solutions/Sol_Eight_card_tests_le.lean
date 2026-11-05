-- Prove2me | solution 1 for Eight.card_tests_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:04:31.042409+00:00
-- url     : https://prove2.me/submissions/c51c67af-ca5f-4345-91a2-3e2fb36544d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Eight_mem_occurring
import Theorems.Thm_Eight_mem_occurrencesOf
import Theorems.Thm_Eight_card_occurrences_le
import Theorems.Thm_Eight_card_tests_add
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_SatNet_lit_mem
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : #(tests g Φ) ≤ 3 * Φ.length - 1 := by
  have h1 := card_tests_add hg h3
  have h2 := card_occurrences_le g Φ
  have h4 : 0 < #(occurrences g Φ) → 0 < #(occurring Φ) := by
    intro h
    obtain ⟨p, hp⟩ := Finset.card_pos.1 h
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 (mem_occurrencesOf.1 hp)
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    exact Finset.card_pos.2 ⟨l.1, mem_occurring.2 ⟨C, hC, l, hlC, rfl⟩⟩
  omega
end Eight
