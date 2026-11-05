-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.ext_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:32.384072+00:00
-- url     : https://prove2.me/submissions/a426c3be-f482-40e9-9ff3-5d56501ae8e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r : ℕ} (σ : Fin (n + r) → Bool) {v : ℕ} (h : v < n) : ext σ v = ext (xi σ) v := by
  rw [Mark.ext, Mark.ext, dif_pos h, dif_pos (by omega)]
  rfl
end ClauseBound.ParityChecks.BridgeInc
