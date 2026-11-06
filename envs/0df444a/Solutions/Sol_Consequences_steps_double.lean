-- Prove2me | solution 1 for Consequences.steps_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:29:47.355516+00:00
-- url     : https://prove2.me/submissions/42819313-4f5f-4b75-8ef7-9b466dbe52d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_SplitCount_Main
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Consequences_Sets

set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SizeCircuit Complement
namespace Consequences
theorem _root_.solution (c : ℕ) {x : ℝ} (hx : 0 ≤ x) : (c : ℝ) * x ≤ ((2 * c : ℕ) : ℝ) * x := by
  refine mul_le_mul_of_nonneg_right ?_ hx
  exact_mod_cast (by omega : c ≤ 2 * c)
end Consequences
