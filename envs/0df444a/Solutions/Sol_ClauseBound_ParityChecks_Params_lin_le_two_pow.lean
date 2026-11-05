-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.lin_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:36:58.231569+00:00
-- url     : https://prove2.me/submissions/41243657-35c8-4a8c-b39b-1c2f7bb278f4

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
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (ℓ : ℕ) (h : 12 ≤ ℓ) : 200 * ℓ + 300 ≤ 2 ^ ℓ := by
  induction ℓ, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega
end ClauseBound.ParityChecks.Params
