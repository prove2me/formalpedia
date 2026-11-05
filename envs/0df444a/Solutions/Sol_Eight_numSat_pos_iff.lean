-- Prove2me | solution 1 for Eight.numSat_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:36:23.072192+00:00
-- url     : https://prove2.me/submissions/d9805d80-5ddc-484f-acc9-8dfc16c456a4

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
import Theorems.Thm_Eight_continued_of_mem
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution (Φ : Formula) : 0 < numSat Φ ↔ Φ.Sat := by
  unfold numSat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨continued a, fun C hC => ?_⟩
    obtain ⟨l, hl, h, e⟩ := (Finset.mem_filter.1 ha).2 C hC
    exact ⟨l, hl, by rw [continued_of_mem a h, e]⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun v => a v.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩⟩
    obtain ⟨l, hl, e⟩ := ha C hC
    exact ⟨l, hl, mem_occurring.2 ⟨C, hC, l, hl, rfl⟩, e⟩
end Eight
