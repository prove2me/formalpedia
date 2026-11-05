-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.mul_succ_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:36:53.88024+00:00
-- url     : https://prove2.me/submissions/76e5d140-0d22-445c-b6ea-3e0006aa72c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (x : ℕ) : x * (x + 1) ≤ 2 ^ (x + 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have h : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
    rw [pow_succ] at ih ⊢
    rw [pow_succ]
    nlinarith
end ClauseBound.ParityChecks.Params
