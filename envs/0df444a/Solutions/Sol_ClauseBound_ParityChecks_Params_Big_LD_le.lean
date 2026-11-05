-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.LD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:47.333322+00:00
-- url     : https://prove2.me/submissions/5ec78a85-2ebe-463a-91ab-44725dab5995

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c

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
theorem _root_.solution : LD Δ ≤ 1 + c * t := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_one]
  exact Nat.mul_le_mul_left _ b.Δ_le
end ClauseBound.ParityChecks.Params.Big
