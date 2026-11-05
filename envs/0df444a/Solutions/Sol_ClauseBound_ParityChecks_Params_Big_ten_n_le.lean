-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.ten_n_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:06.048356+00:00
-- url     : https://prove2.me/submissions/f527009e-746c-43a7-b3fe-509fe3342873

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
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
theorem _root_.solution : 10 * n ≤ (ℓ - ℓ / 2) * i0Of n := by
  have h1 := b.i0_spec.1
  have h2 : ℓ * i0Of n ≤ 2 * (ℓ - ℓ / 2) * i0Of n := Nat.mul_le_mul_right _ (by omega)
  have e : 2 * (ℓ - ℓ / 2) * i0Of n = 2 * ((ℓ - ℓ / 2) * i0Of n) := by ring
  omega
end ClauseBound.ParityChecks.Params.Big
