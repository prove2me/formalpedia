-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:01.711216+00:00
-- url     : https://prove2.me/submissions/e808bfef-0d1d-4f64-8a8a-880e783e7cbe

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
theorem _root_.solution : ℓ + 1 ≤ 2 ^ t := by
  rw [b.ht]; exact Nat.le_pow_clog (by norm_num) _
end ClauseBound.ParityChecks.Params.Big
