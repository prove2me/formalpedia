-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.getD_append_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:34.862447+00:00
-- url     : https://prove2.me/submissions/9a8d0f24-d6a0-44e9-91ce-5b3a0009dba7

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
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (Ls : List Chk) (c : Chk) : (Ls ++ [c]).getD Ls.length [] = c := by
  simp [List.getD_eq_getElem?_getD]
end ClauseBound.ParityChecks.Run
