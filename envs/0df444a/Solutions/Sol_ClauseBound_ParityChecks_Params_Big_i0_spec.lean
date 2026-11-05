-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.i0_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:36:35.315794+00:00
-- url     : https://prove2.me/submissions/346962dc-1697-4c72-b006-2616fa43b0c8

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
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : 20 * n ≤ ℓ * i0Of n ∧ ℓ * i0Of n ≤ 20 * n + ℓ - 1 := by
  have hℓ1 := b.hℓ1
  unfold i0Of
  rw [← b.hℓ]
  have h1 := Nat.lt_mul_div_succ (20 * n + ℓ - 1) (show 0 < ℓ by omega)
  have h2 := Nat.mul_div_le (20 * n + ℓ - 1) ℓ
  rw [mul_add, mul_one] at h1
  constructor <;> omega
end ClauseBound.ParityChecks.Params.Big
