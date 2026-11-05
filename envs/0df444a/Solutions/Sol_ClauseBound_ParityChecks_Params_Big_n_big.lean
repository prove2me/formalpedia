-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.n_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:38:56.29534+00:00
-- url     : https://prove2.me/submissions/a6e960b2-35b7-43f0-9239-d39a7984ac1f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_lin_le_two_pow
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n

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
theorem _root_.solution : 200 * ℓ + 300 ≤ n :=
  le_trans (lin_le_two_pow ℓ (by have := b.ℓ_ge; omega)) b.pow_le_n
end ClauseBound.ParityChecks.Params.Big
