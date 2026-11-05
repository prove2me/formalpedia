-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.eq_of_foldl_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:17.071624+00:00
-- url     : https://prove2.me/submissions/6369f3d0-6c5a-434a-9b48-17d8d90ea534

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_ClauseBound_Alg_NeedC_foldl_none
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (P : PiecesF) (pad : U) (sched : List Step) (st st' : NState)
    (h : sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some st') :
    st' = sched.foldl (needStep P) st := by
  induction sched generalizing st with
  | nil => exact (Option.some.inj h).symm
  | cons s r ih =>
    rw [List.foldl_cons, Option.map_some] at h
    by_cases hl : len (some (needStep P st s)) ≤ pad.length
    · rw [cap_eq hl] at h
      exact ih _ h
    · rw [show cap pad none (some (needStep P st s)) = none from if_neg hl, foldl_none] at h
      cases h
end ClauseBound.Alg.NeedC
