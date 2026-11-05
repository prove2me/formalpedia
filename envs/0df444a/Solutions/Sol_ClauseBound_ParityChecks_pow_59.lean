-- Prove2me | solution 1 for ClauseBound.ParityChecks.pow_59
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:34:48.111537+00:00
-- url     : https://prove2.me/submissions/4716489d-96f3-412d-9531-449709438ec3

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
namespace ClauseBound.ParityChecks
theorem _root_.solution : (2 : ℚ) ^ 40 ≤ (8 / 5) ^ 59 := by norm_num
end ClauseBound.ParityChecks
