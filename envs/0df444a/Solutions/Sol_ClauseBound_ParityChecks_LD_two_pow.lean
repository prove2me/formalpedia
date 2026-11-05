-- Prove2me | solution 1 for ClauseBound.ParityChecks.LD_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:37:25.705146+00:00
-- url     : https://prove2.me/submissions/2d7d77b9-71c1-46b4-b85a-f7c089c4b456

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_ParityChecks_ArithAux

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks
theorem _root_.solution (β : ℕ) : LD (2 ^ β) = β + 1 := by
  rw [LD, ← pow_succ', Nat.clog_pow 2 _ (by norm_num)]
end ClauseBound.ParityChecks
