-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:26.969493+00:00
-- url     : https://prove2.me/submissions/ea857ee6-7b0f-43c8-9a77-0365b670ac32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_lt_two_mul
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_spec
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : 6 * m * 2 ^ (ℓ - ℓ / 2) ≤ nbOf n Δ * i0Of n := by
  have hLD := b.two_le_LD
  have hℓ1 := b.hℓ1
  have hpos : 0 < 2 * LD Δ * ℓ := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  have h1 : 12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2) ≤ n := by
    calc 12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2) ≤ 2 ^ (ℓ / 2) * 2 ^ (ℓ - ℓ / 2) := Nat.mul_le_mul_right _ b.poly_le
      _ = 2 ^ ℓ := by rw [← pow_add]; congr 1; omega
      _ ≤ n := b.pow_le_n
  calc 6 * m * 2 ^ (ℓ - ℓ / 2) * (2 * LD Δ * ℓ) ≤ 6 * (Δ * n) * 2 ^ (ℓ - ℓ / 2) * (2 * LD Δ * ℓ) := by
        have := b.hm; gcongr
    _ = n * (12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2)) := by ring
    _ ≤ n * n := Nat.mul_le_mul_left _ h1
    _ ≤ (2 * (nbOf n Δ * LD Δ)) * (ℓ * i0Of n) := Nat.mul_le_mul b.lt_two_mul.le (by have := b.i0_spec.1; omega)
    _ = nbOf n Δ * i0Of n * (2 * LD Δ * ℓ) := by ring
end ClauseBound.ParityChecks.Params.Big
