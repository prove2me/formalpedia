-- Prove2me | solution 1 for Consequences.size_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:40.17142+00:00
-- url     : https://prove2.me/submissions/1d44e27e-9c03-4068-b12a-6b5db8e588b9

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
theorem _root_.solution {c n m : ℕ} (hm : m ≤ n * n) : c * (n + m + 2) ^ c ≤ 2 * c * (n + 2) ^ (2 * c) := by
  have h1 : n + m + 2 ≤ (n + 2) ^ 2 := by nlinarith
  calc c * (n + m + 2) ^ c ≤ c * ((n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 c)
    _ = c * (n + 2) ^ (2 * c) := by rw [← pow_mul]
    _ ≤ 2 * c * (n + 2) ^ (2 * c) := Nat.mul_le_mul_right _ (by omega)
end Consequences
