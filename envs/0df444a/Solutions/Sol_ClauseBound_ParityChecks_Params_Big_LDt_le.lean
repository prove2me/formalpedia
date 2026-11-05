-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.LDt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:47.956455+00:00
-- url     : https://prove2.me/submissions/fc468449-0f0c-4ed4-8bad-23ffc37fb4a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_t_pos
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LD_le

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
theorem _root_.solution : 42 * (LD Δ + t) ≤ ℓ := by
  have := b.LD_le; have := b.hA'; have := b.t_pos; omega
end ClauseBound.ParityChecks.Params.Big
