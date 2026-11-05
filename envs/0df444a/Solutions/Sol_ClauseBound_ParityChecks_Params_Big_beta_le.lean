-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.beta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:45:00.992199+00:00
-- url     : https://prove2.me/submissions/5b343300-feee-4e17-b1c1-ad9e28d077f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_big
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_beta0_le__7e166ed85866
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta1_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta1_small

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
theorem _root_.solution : n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 ≤ 5 * n := by
  have h1 := b.beta0_le'
  have h2 := b.LDt_le
  have h3 := b.n_big
  have h4 := b.beta1_le
  have h5 := b.beta1_small
  omega
end ClauseBound.ParityChecks.Params.Big
