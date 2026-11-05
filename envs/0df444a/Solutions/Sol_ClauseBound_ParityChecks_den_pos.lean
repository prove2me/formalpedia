-- Prove2me | solution 1 for ClauseBound.ParityChecks.den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:32.860839+00:00
-- url     : https://prove2.me/submissions/302033db-3b7b-489e-ab7c-bda6862dac84

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
namespace ClauseBound.ParityChecks
theorem _root_.solution (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) (hr : 1 ≤ q.r) (j : ℕ) : 0 < q.den j := by
  unfold Par.den
  positivity
end ClauseBound.ParityChecks
