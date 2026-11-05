-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.needFin_foldl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:56.481195+00:00
-- url     : https://prove2.me/submissions/622da454-55fb-4f58-934b-5ed9c91e3742

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_ClauseBound_Alg_NeedC_tot_cons

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (P : PiecesF) (sched : List Step) (st : NState) : needFin (sched.foldl (needStep P) st) = tot P st sched := by
  induction sched generalizing st with
  | nil => rfl
  | cons s r ih => rw [List.foldl_cons, ih, tot_cons]
end ClauseBound.Alg.NeedC
