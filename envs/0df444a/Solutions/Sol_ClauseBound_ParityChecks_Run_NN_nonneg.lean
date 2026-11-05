-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.NN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:37.333109+00:00
-- url     : https://prove2.me/submissions/d761d1ec-eaf8-42bb-b516-e36a7e06568e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution : 0 ≤ NN X q := Nat.cast_nonneg _
end ClauseBound.ParityChecks.Run
