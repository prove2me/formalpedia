-- Prove2me | solution 1 for ClauseBound.ParityChecks.Sizes.mul_qv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:41.090706+00:00
-- url     : https://prove2.me/submissions/32a5923f-a70d-4b68-92e4-9e1452eec3f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound.ParityChecks.Sizes
namespace ClauseBound.ParityChecks.Sizes
theorem _root_.solution (g N : ℕ) : g * qv g N ≤ N + g - 1 := Nat.mul_div_le _ _
end ClauseBound.ParityChecks.Sizes
