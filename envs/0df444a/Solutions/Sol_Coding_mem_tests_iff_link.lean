-- Prove2me | solution 1 for Coding.mem_tests_iff_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:04:49.011787+00:00
-- url     : https://prove2.me/submissions/b7e6a7d3-c84a-4757-9210-e610be82bb99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Coding_place_occOfSlot
import Theorems.Thm_Coding_mem_occurrencesOf_iff
import Theorems.Thm_Coding_mem_tests_iff
import Theorems.Thm_Eight_mem_occurrencesOf
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) (p q : Slot 1 Φ.length 3) : (occOfSlot p, occOfSlot q) ∈ tests Φ ↔ Link Φ p q := by
  rw [mem_tests_iff h3, place_occOfSlot, place_occOfSlot, linkB_iff (by omega)]
  refine ⟨fun h => h.2.2, fun l => ⟨?_, ?_, l⟩⟩
  · refine (mem_occurrencesOf_iff p).1 (mem_occurrencesOf.2 fun h => l.2.1 ?_)
    rw [lab, h]; rfl
  · refine (mem_occurrencesOf_iff q).1 (mem_occurrencesOf.2 fun h => l.2.1 ?_)
    rw [l.2.2.1, lab, h]; rfl
end Coding
