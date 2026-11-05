-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:36:52.593367+00:00
-- url     : https://prove2.me/submissions/7c72b5cd-e181-4773-9363-f0f7357146bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_pow_59

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (X r : ℕ) (h : 59 * X ≤ 40 * r) : (2 : ℚ) ^ X ≤ (8 / 5) ^ r := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show 40 ≠ 0 by norm_num)).1
  calc ((2 : ℚ) ^ X) ^ 40 = (2 ^ 40) ^ X := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ ((8 / 5) ^ 59) ^ X := pow_le_pow_left₀ (by positivity) pow_59 X
    _ = (8 / 5) ^ (59 * X) := by rw [← pow_mul]
    _ ≤ (8 / 5) ^ (40 * r) := pow_le_pow_right₀ (by norm_num) h
    _ = ((8 / 5 : ℚ) ^ r) ^ 40 := by rw [← pow_mul, mul_comm]
end ClauseBound.ParityChecks.Params
