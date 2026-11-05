-- Prove2me | solution 1 for ClauseBound.ParityChecks.Sizes.two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:45:33.801546+00:00
-- url     : https://prove2.me/submissions/76d8aaec-637c-41c6-9a9e-fccd87ba6dec

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
theorem _root_.solution (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
end ClauseBound.ParityChecks.Sizes
