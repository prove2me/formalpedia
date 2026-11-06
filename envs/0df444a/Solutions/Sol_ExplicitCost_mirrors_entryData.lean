-- Prove2me | solution 1 for ExplicitCost.mirrors_entryData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:19:31.8148+00:00
-- url     : https://prove2.me/submissions/beae6efd-1dbf-4c91-bd44-16a119051a84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_widen
import Theorems.Thm_P2M_ExplicitCost_size_widen__a57a929d61ba
import Theorems.Thm_ExplicitCost_nPairs_widen
import Theorems.Thm_ExplicitCost_nStates_widen
import Theorems.Thm_ExplicitCost_validB_widen
import Theorems.Thm_ExplicitCost_mirrors_termData
import Theorems.Thm_ExplicitCost_Mirrors_ite
import Theorems.Thm_ExplicitCost_Mirrors_mono
import Theorems.Thm_ExplicitCost_Mirrors_prodRange
import Theorems.Thm_ExplicitCost_Mirrors_sumRange
import Theorems.Thm_ExplicitCost_mirrors_const
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors (tableQ K g asked) entryData (widen K g) (4 * (2 * K + 2 * g + 2)) :=
  Mirrors.ite
    (Mirrors.sumRange (d₁ := 3 * (2 * K + 2 * g + 2))
      (Mirrors.prodRange (mirrors_termData K g) (nPairs_widen K g) (size_widen₁ K g) (by omega))
      (nStates_widen K g) (fun u => (size_widen K g u).le) (by omega))
    ((mirrors_const 0 fun u => (size_widen K g u).le).mono (by omega)) (validB_widen K g)
end ExplicitCost
