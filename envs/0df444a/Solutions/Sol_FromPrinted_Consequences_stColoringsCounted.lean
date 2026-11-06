-- Prove2me | solution 1 for FromPrinted.Consequences.stColoringsCounted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:34.211143+00:00
-- url     : https://prove2.me/submissions/0f84d24b-ee39-425e-9283-1ddf16e12f29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_Consequences_Sets
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sets
import Theorems.Thm_Eight_ViaGrouping_COLOR_counts_of
import Theorems.Thm_FromPrinted_SplitCount_stEngineCounts


set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement
namespace FromPrinted.Consequences
theorem _root_.solution : StColoringsCounted := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, hp, c, h⟩ := COLOR_counts_of stEngineCounts k (by omega) hδ
  exact ⟨ℓ, τ, c, hp, h⟩
end FromPrinted.Consequences
