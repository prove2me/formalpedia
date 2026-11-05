-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.lt_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:44:15.394557+00:00
-- url     : https://prove2.me/submissions/3317dfdd-1c1a-45bb-b4d7-b102480144a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_lt_succ_mul
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_nb

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
theorem _root_.solution : n < 2 * (nbOf n Δ * LD Δ) := by
  have h1 := b.lt_succ_mul
  have h2 : LD Δ ≤ nbOf n Δ * LD Δ := Nat.le_mul_of_pos_left _ (by have := b.two_le_nb; omega)
  rw [add_mul, one_mul] at h1
  omega
end ClauseBound.ParityChecks.Params.Big
