-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.ext_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:33.376274+00:00
-- url     : https://prove2.me/submissions/267bc4fe-e74b-49ae-bf68-a8444e78d337

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
theorem _root_.solution {n r : ℕ} (σ : Fin (n + r) → Bool) (j : Fin r) : ext σ (n + j.val) = yy σ j := by
  rw [Mark.ext, dif_pos (by omega)]
  rfl
end ClauseBound.ParityChecks.BridgeInc
