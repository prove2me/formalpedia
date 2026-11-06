-- Prove2me | solution 1 for CircuitLowerBound.stRestart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:11:01.516536+00:00
-- url     : https://prove2.me/submissions/17f3bb29-681b-4b35-8a4c-d9be4270606f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Theorems.Thm_CircuitLowerBound_Oracle_initList_otm
import Theorems.Thm_CircuitLowerBound_Oracle_haltList_otm
import Theorems.Thm_CircuitLowerBound_Oracle_time_le
import Theorems.Thm_CircuitLowerBound_Oracle_run_protocol
import Theorems.Thm_Groundwork_Stepped_Reaches_iterate
import Theorems.Thm_Groundwork_TM_Run_iterate
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Groundwork.TM
open Oracle
namespace CircuitLowerBound
theorem _root_.solution : StRestart := by
  rintro L ⟨M, c, hfin, h⟩
  refine ⟨otm M, 2 * c + 7, fun k => ?_, fun x => ?_⟩
  · rcases k with k | j
    · exact hfin k
    · exact (inferInstance : Finite Bool)
  · obtain ⟨b, hb, hP⟩ := h x
    obtain ⟨t, ht, hr⟩ := run_protocol hP
    refine ⟨b, hb, ⟨⟨⟨t, ?_⟩, ht.trans (time_le c x.length)⟩⟩⟩
    rw [initList_otm, haltList_otm]
    exact hr.iterate
end CircuitLowerBound
