-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.nb_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:55.654756+00:00
-- url     : https://prove2.me/submissions/e7e178bf-b00c-4e7d-bcdc-3b0d0e4cdf38

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
theorem _root_.solution (n Δ : ℕ) : nbOf n Δ * LD Δ ≤ n := Nat.div_mul_le_self _ _
end ClauseBound.ParityChecks.Params
