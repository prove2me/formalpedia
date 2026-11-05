-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.foldl_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:49:50.431999+00:00
-- url     : https://prove2.me/submissions/4858ba4f-9ffc-48e6-a934-ef759d565790

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (P : PiecesF) (pad : U) (sched : List Step) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (none : Option NState) = none := by
  induction sched with
  | nil => rfl
  | cons s r ih =>
    have h : cap pad none ((none : Option NState).map fun st => needStep P st s) = none := by
      unfold cap
      split_ifs <;> rfl
    rw [List.foldl_cons, h, ih]
end ClauseBound.Alg.NeedC
