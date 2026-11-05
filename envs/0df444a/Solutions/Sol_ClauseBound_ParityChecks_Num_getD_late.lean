-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.getD_late
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:14.334242+00:00
-- url     : https://prove2.me/submissions/6942b0e4-1a80-4a47-9c6c-7b3c52f72b7d

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
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (Ls : List Chk) (cur : Chk) (i : ℕ) : (Ls ++ [cur]).getD (Ls.length + 1 + i) [] = [] := by
  apply List.getD_eq_default
  simp only [List.length_append, List.length_singleton]
  omega
end ClauseBound.ParityChecks.Num
