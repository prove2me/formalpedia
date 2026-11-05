-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.runChecks_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:15.482056+00:00
-- url     : https://prove2.me/submissions/c5a32b48-0b8f-4049-985b-a43b08794847

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
theorem _root_.solution (j : ℕ) :
    q.runChecks orcA orcB (j + 1) = q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m] := by
  unfold Par.runChecks
  rw [List.range_succ, List.foldl_append]
  rfl
end ClauseBound.ParityChecks.Run
