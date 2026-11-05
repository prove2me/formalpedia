-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.beta0_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:44:43.711372+00:00
-- url     : https://prove2.me/submissions/f1996c91-28bd-46eb-8809-561ae84ff1e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_big
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_beta0_le__7e166ed85866

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
theorem _root_.solution : beta0 m (nbOf n Δ) ≤ 4 * n := by
  have h1 := b.beta0_le'
  have h2 := b.LDt_le
  have h3 := b.n_big
  omega
end ClauseBound.ParityChecks.Params.Big
