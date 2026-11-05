-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.two_mul_sig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:06.657586+00:00
-- url     : https://prove2.me/submissions/fb693267-6848-4570-bb52-045e3a971b7c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution (i : ℕ) : 2 * sig i = (-2) ^ i + if i = 0 then 1 else 0 := by
  unfold sig
  cases i with
  | zero => simp
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow, pow_succ (2 : ℤ) k]
    ring
end ClauseBound.ParityChecks.StepOne
