-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.beta0_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:39:48.774235+00:00
-- url     : https://prove2.me/submissions/47f24bf6-c4a4-4e8e-9fa3-fdce77eea5b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_two_pow
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_lt_succ_mul

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
theorem _root_.solution : beta0 m (nbOf n Δ) ≤ 3 * LD Δ * (nbOf n Δ + 1) := by
  apply Nat.clog_le_of_le_pow
  apply choose_le_two_pow (by omega) b.hnb le_rfl
  have h1 := (two_Δ_le Δ)
  have h2 : LD Δ ≤ 2 ^ LD Δ := Nat.lt_two_pow_self.le
  have h3 : 3 ≤ 2 ^ LD Δ := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ LD Δ := Nat.pow_le_pow_right (by norm_num) b.two_le_LD
  have h4 : Δ ≤ 2 ^ LD Δ := by omega
  have h5 : 2 ^ (3 * LD Δ) = 2 ^ LD Δ * 2 ^ LD Δ * 2 ^ LD Δ := by
    rw [show 3 * LD Δ = LD Δ + LD Δ + LD Δ by ring, pow_add, pow_add]
  rw [h5]
  calc 3 * m ≤ 3 * (Δ * ((nbOf n Δ + 1) * LD Δ)) :=
        Nat.mul_le_mul_left _ (le_trans b.hm (Nat.mul_le_mul_left _ b.lt_succ_mul.le))
    _ = (nbOf n Δ + 1) * (3 * Δ * LD Δ) := by ring
    _ ≤ (nbOf n Δ + 1) * (2 ^ LD Δ * 2 ^ LD Δ * 2 ^ LD Δ) := by gcongr
end ClauseBound.ParityChecks.Params.Big
