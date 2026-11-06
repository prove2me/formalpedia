-- Prove2me | solution 1 for Consequences.ofWord_binary_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:51.871638+00:00
-- url     : https://prove2.me/submissions/7871e7ac-4590-48e7-b4f1-059b8626de59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_Consequences_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Consequences_Main
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_ofWord_toWord
import Theorems.Thm_SplitCount_toWord_eq


set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount Turing
namespace Consequences
theorem _root_.solution {N v : ℕ} (h : v < 2 ^ (N + 1)) : ofWord (SatK.binary N v) = v := by
  rw [SatK.binary, ← SplitCount.toWord_eq, ofWord_toWord h]
end Consequences
