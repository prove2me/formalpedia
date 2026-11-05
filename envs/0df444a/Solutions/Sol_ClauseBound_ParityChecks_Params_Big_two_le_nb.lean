-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.two_le_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:41:09.852491+00:00
-- url     : https://prove2.me/submissions/278a99df-0ac2-4642-a45c-eee7e4969a97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_big
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le

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
theorem _root_.solution : 2 ≤ nbOf n Δ := by
  unfold nbOf
  rw [Nat.le_div_iff_mul_le (by have := b.two_le_LD; omega)]
  have := b.LDt_le; have := b.n_big; omega
end ClauseBound.ParityChecks.Params.Big
