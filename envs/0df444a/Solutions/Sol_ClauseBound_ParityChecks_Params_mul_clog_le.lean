-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.mul_clog_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:38:44.697233+00:00
-- url     : https://prove2.me/submissions/99cc67ca-9090-4401-b4c8-da63c8b2677e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_mul_succ_le_two_pow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (A ℓ : ℕ) (hA : 1 ≤ A) (hℓ : 2 * A ^ 2 ≤ ℓ) : A * Nat.clog 2 (ℓ + 1) ≤ ℓ := by
  have h1 : ℓ < A * (ℓ / A + 1) := Nat.lt_mul_div_succ ℓ hA
  have h2 : 2 * A ≤ ℓ / A := by
    rw [Nat.le_div_iff_mul_le hA]
    calc 2 * A * A = 2 * A ^ 2 := by ring
      _ ≤ ℓ := hℓ
  have h3 := mul_succ_le_two_pow (ℓ / A)
  have h4 : ℓ + 1 ≤ 2 ^ (ℓ / A) := by
    generalize ℓ / A = x at *
    have h5 : 2 * A * (x + 1) ≤ x * (x + 1) := Nat.mul_le_mul_right _ h2
    rw [pow_succ] at h3
    nlinarith
  calc A * Nat.clog 2 (ℓ + 1) ≤ A * (ℓ / A) := Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow h4)
    _ ≤ ℓ := Nat.mul_div_le _ _
end ClauseBound.ParityChecks.Params
