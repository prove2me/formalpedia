-- Prove2me | solution 1 for FromPrinted.SplitCount.stEngineCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:37.041047+00:00
-- url     : https://prove2.me/submissions/76d58121-5429-4e41-83a7-0297dd4783e0

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
import Theorems.Thm_FromPrinted_SplitCount_COUNT_polyTimeSteps
import Theorems.Thm_FromPrinted_SplitCount_stCountsAt
import Theorems.Thm_CountKSat_Poly_certStepC
import Theorems.Thm_Eight_Level_exists_level
import Theorems.Thm_Exits_COUNT_polyTimeSteps
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitCount_deltaPrime_facts
import Theorems.Thm_SplitCount_stCert
import Theorems.Thm_SplitCount_stCountsAt
import Theorems.Thm_SplitCount_stStepTwo


set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution : StEngineCounts := by
  intro k hk δ hδ
  -- «choosing ε = δ/3 first»
  obtain ⟨τ, Dd, Bl, Sk, hsp⟩ := stStepTwo k (δ / 3) (by positivity)
  -- «and then applying Theorem 2 with a small enough value in place of δ»
  obtain ⟨h0, -, -⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨ℓ, a1, a2⟩ := Level.exists_level (η := deltaPrime δ (max k 3) Bl / 12) (by positivity) ⌈72 / deltaPrime δ (max k 3) Bl⌉₊
  exact ⟨ℓ, τ, stCert.2 _ _ (Poly.certStepC _ k) (stCert.1 _ (COUNT_polyTimeSteps ℓ)),
    stCountsAt k hk δ hδ _ Dd Bl Sk hsp ℓ ((Nat.le_ceil _).trans (by exact_mod_cast a1)) a2⟩
end FromPrinted.SplitCount
