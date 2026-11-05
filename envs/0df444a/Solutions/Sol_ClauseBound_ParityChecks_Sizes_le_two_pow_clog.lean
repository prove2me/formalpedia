-- Prove2me | solution 1 for ClauseBound.ParityChecks.Sizes.le_two_pow_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:45:52.808882+00:00
-- url     : https://prove2.me/submissions/2d3c227c-0eb4-41d9-b206-33d04902da3e

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
theorem _root_.solution (n : ℕ) : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) _
end ClauseBound.ParityChecks.Sizes
