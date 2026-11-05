-- Prove2me | solution 1 for ClauseBound.ParityChecks.clog_le_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:46:24.806656+00:00
-- url     : https://prove2.me/submissions/ca553667-36c6-43a5-8f09-d07d3d736228

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
theorem _root_.solution (n : ℕ) : Nat.clog 2 n ≤ Nat.size n :=
  Nat.clog_le_of_le_pow (Nat.lt_size_self n).le
end ClauseBound.ParityChecks
