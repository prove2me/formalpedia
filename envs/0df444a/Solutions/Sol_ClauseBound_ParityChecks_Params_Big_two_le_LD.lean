-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.two_le_LD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:27:58.97075+00:00
-- url     : https://prove2.me/submissions/49b6122c-b8ec-4ef1-bc5c-2bcb283c5194

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
theorem _root_.solution : 2 ≤ LD Δ := by
  have h : 1 < LD Δ := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by have := b.hΔ2; omega)
  exact h
end ClauseBound.ParityChecks.Params.Big
