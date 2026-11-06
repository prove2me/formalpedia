-- Prove2me | solution 1 for FromPrinted.Consequences.circuitsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:58:07.436169+00:00
-- url     : https://prove2.me/submissions/b4bf46b6-a194-45e0-8746-266d7b130416

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Circuits
import Theorems.Thm_CircuitLowerBound_corCircuits_of
import Theorems.Thm_Eight_ViaGrouping_corCircuitsInf_of
import Theorems.Thm_Eight_ViaGrouping_corCircuits_of
import Theorems.Thm_Eight_ViaGrouping_stEngine_of
import Theorems.Thm_P2M_CircuitLowerBound_corCircuits__of_9b88f614dd99
import Theorems.Thm_P2M_Eight_ViaGrouping_corCircuits__of_02487e33d61e


set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing
namespace FromPrinted.Consequences
theorem _root_.solution (h : EngineCounts ENGINEsplit) : Circuits :=
  ⟨corCircuits_of (stEngine_of h), corCircuits'_of (stEngine_of h), corCircuitsInf_of (stEngine_of h)⟩
end FromPrinted.Consequences
