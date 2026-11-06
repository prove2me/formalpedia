-- Prove2me | solution 1 for CircuitLowerBound.Clause.fbit_dq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:50.593204+00:00
-- url     : https://prove2.me/submissions/3af7f01e-b9de-4dbf-b10e-0b5ac7d32b9b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (kbm i : ℕ) (l : TLit) : fbit kbm l (5 + kbm + i) = l.2.2.2.1.testBit i := by
  unfold fbit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega
end CircuitLowerBound.Clause
