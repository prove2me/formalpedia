-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.choose_le_beta0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:39.798439+00:00
-- url     : https://prove2.me/submissions/f60ca809-1074-4f95-a976-569176c079cc

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
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (m nb : ℕ) : m.choose (nb + 1) ≤ 2 ^ beta0 m nb := Nat.le_pow_clog (by norm_num) _
end ClauseBound.ParityChecks.Params
