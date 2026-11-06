-- Prove2me | solution 1 for FromPrinted.SplitCount.stCountsWithAnyCliqueAlgorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:09.558857+00:00
-- url     : https://prove2.me/submissions/daeb13a9-bb74-4c8e-b7a9-e77ac35a8234

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Count
import Theorems.Thm_FromPrinted_SplitCount_stComputesZ
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_SplitCount_deltaPrime_facts
import Theorems.Thm_SplitCount_stComputesZ
import Theorems.Thm_SplitCount_stStepOneFor
import Theorems.Thm_SplitCount_stSuffices
import Theorems.Thm_Suffices_stSuffices
import Theorems.Thm_WidthK_InvK_step


set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution : StCountsWithAnyCliqueAlgorithm := by
  intro k hk δ hδ step Dd Bl Sk hsp K M Cc hK2 hK hM
  obtain ⟨h0, h1, h2⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨A, hA⟩ := stComputesZ _ h0 h1 K M Cc hK2 hK hM
  obtain ⟨A', hA'⟩ := stStepOneFor _ _ A h0.le hA
  exact stSuffices k hk δ hδ step Dd Bl Sk hsp _ _ A' h0.le h2 hA'
end FromPrinted.SplitCount
