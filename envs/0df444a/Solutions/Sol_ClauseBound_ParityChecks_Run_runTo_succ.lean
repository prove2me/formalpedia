-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.runTo_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:31.867205+00:00
-- url     : https://prove2.me/submissions/ed801bee-3b9d-4685-ac45-9c1a875f7e27

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
variable {V} {orcA orcB} {ε : ℚ}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (Ls : List Chk) (e : ℕ) : q.runTo orcA orcB Ls (e + 1) = q.decide1 orcA orcB Ls (q.runTo orcA orcB Ls e) e := by
  unfold Par.runTo
  rw [List.range_succ, List.foldl_append]
  rfl
end ClauseBound.ParityChecks.Run
