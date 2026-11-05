-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.beta1_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:41:12.934228+00:00
-- url     : https://prove2.me/submissions/d1c3bc14-c41d-4f5e-b57f-bbba021b28fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_big
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_spec

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
theorem _root_.solution : 2 * ((LD Δ + t) * i0Of n) ≤ n := by
  have h1 : 42 * (LD Δ + t) * i0Of n ≤ ℓ * i0Of n := Nat.mul_le_mul_right _ b.LDt_le
  have h2 := b.i0_spec.2
  have h3 := b.n_big
  have e : 42 * (LD Δ + t) * i0Of n = 42 * ((LD Δ + t) * i0Of n) := by ring
  omega
end ClauseBound.ParityChecks.Params.Big
