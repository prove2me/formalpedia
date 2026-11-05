-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.beta1_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:39:07.428997+00:00
-- url     : https://prove2.me/submissions/5a286005-1fe8-45ba-85bf-68ef1aeb572b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_two_pow
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_t_pos
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_succ_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_spec
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_pos

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
theorem _root_.solution : beta1 m (i0Of n) ≤ (LD Δ + t) * i0Of n := by
  unfold beta1
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ i0Of n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  apply Nat.clog_le_of_le_pow
  by_cases h : i0Of n ≤ m
  · apply choose_le_two_pow b.i0_pos h hi'
    rw [pow_add]
    have h1 : 2 * Δ * (ℓ + 1) ≤ 2 ^ LD Δ * 2 ^ t := Nat.mul_le_mul (two_Δ_le Δ) b.succ_le
    calc 3 * m ≤ 3 * (Δ * n) := Nat.mul_le_mul_left _ b.hm
      _ ≤ 2 * Δ * (20 * n) := by nlinarith [Nat.zero_le (Δ * n)]
      _ ≤ 2 * Δ * (ℓ * i0Of n) := Nat.mul_le_mul_left _ b.i0_spec.1
      _ ≤ 2 * Δ * ((ℓ + 1) * i0Of n) := by gcongr; omega
      _ = i0Of n * (2 * Δ * (ℓ + 1)) := by ring
      _ ≤ i0Of n * (2 ^ LD Δ * 2 ^ t) := Nat.mul_le_mul_left _ h1
  · refine le_trans (Nat.choose_le_two_pow m i) (Nat.pow_le_pow_right (by norm_num) ?_)
    have h2 : i0Of n ≤ (LD Δ + t) * i0Of n := Nat.le_mul_of_pos_left _ (by have := b.t_pos; omega)
    omega
end ClauseBound.ParityChecks.Params.Big
