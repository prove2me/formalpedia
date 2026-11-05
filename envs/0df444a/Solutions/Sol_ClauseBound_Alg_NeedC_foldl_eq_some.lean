-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.foldl_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:40.456609+00:00
-- url     : https://prove2.me/submissions/5fcd9a2d-21de-4a89-972c-eb7922f9b5be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_ClauseBound_Alg_NeedC_tot_cons
import Theorems.Thm_ClauseBound_Alg_NeedC_len_some_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (P : PiecesF) {pad : U} {b : ℕ} (hp : 100 * (b + 2) ≤ pad.length) (sched : List Step) (st : NState)
    (h : tot P st sched ≤ b) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some (sched.foldl (needStep P) st) := by
  induction sched generalizing st with
  | nil => rfl
  | cons s r ih =>
    rw [← tot_cons] at h
    rw [List.foldl_cons, List.foldl_cons, Option.map_some, cap_eq ((len_some_le P _ r h).trans hp)]
    exact ih _ h
end ClauseBound.Alg.NeedC
