-- Prove2me | solution 1 for FromPrinted.SplitCount.stStepOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:47:45.091006+00:00
-- url     : https://prove2.me/submissions/e6e676c9-c142-46df-9d04-70125209578b

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
import Theorems.Thm_FromPrinted_SplitCount_stFirstLine
import Theorems.Thm_FromPrinted_SplitCount_stCountIsNetworkMachine
import Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
import Theorems.Thm_Exits_stClique
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Paper_levelK_ge
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_stClique
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_stComputesZ
import Theorems.Thm_SplitCount_stCountIsNetworkMachine
import Theorems.Thm_SplitCount_stStepOneFor


set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution : StStepOne := by
  intro δ' h0 h1 ℓ hK hE
  obtain ⟨-, Cc, hC⟩ := Printed.stClique ℓ
  obtain ⟨A, hA⟩ := stComputesZ δ' h0 h1 (levelK ℓ) (Printed.CLIQUE ℓ) Cc ((by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)) hK (hC.mono hE)
  obtain ⟨A', hA'⟩ := stFirstLine _ δ' A hA
  rw [← stCountIsNetworkMachine ℓ] at hA'
  exact stStepOneFor (Printed.COUNT ℓ) δ' A' h0.le hA'
end FromPrinted.SplitCount
