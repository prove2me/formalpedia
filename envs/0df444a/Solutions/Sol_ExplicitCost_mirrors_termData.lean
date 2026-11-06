-- Prove2me | solution 1 for ExplicitCost.mirrors_termData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:01:30.397791+00:00
-- url     : https://prove2.me/submissions/16713f80-56ae-4de1-8f20-559b498cc367

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_P2M_ExplicitCost_size_widen__afc97683d577
import Theorems.Thm_ExplicitCost_isOne_widen
import Theorems.Thm_ExplicitCost_isW_widen
import Theorems.Thm_ExplicitCost_isPsi_widen
import Theorems.Thm_ExplicitCost_mirrors_wData
import Theorems.Thm_ExplicitCost_mirrors_psiData
import Theorems.Thm_ExplicitCost_mirrors_fData
import Theorems.Thm_ExplicitCost_Mirrors_ite
import Theorems.Thm_ExplicitCost_Mirrors_mono
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
theorem _root_.solution : Mirrors (termQ K g asked) termData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.ite ((mirrors_const 1 (size_widen₂ K g)).mono (by omega))
    (Mirrors.ite (mirrors_wData K g) (Mirrors.ite (mirrors_psiData K g) (mirrors_fData K g) (isPsi_widen K g)) (isW_widen K g)) (isOne_widen K g)
end ExplicitCost
