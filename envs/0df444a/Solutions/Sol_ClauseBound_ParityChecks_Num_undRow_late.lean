-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.undRow_late
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:08.81324+00:00
-- url     : https://prove2.me/submissions/7fefe784-6521-457a-adbd-5553a37eceaa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (m e j i : ℕ) : undRow j (Dset m e) (j + 1 + i) = m := by
  unfold undRow; rw [if_neg (by omega), if_neg (by omega), Fintype.card_fin]
end ClauseBound.ParityChecks.Num
