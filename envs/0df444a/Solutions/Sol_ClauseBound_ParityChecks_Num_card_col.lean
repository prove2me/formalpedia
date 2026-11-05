-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.card_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:05:58.502211+00:00
-- url     : https://prove2.me/submissions/26da76c6-e66f-488c-984a-6f4341cc6529

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_getD
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_split
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_mid
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_late
import Theorems.Thm_ClauseBound_ParityChecks_Num_countP_eq_sum

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {Ls : List Chk} (cur : Chk) (hj : Ls.length < q.r) (x : Fin q.m) :
    #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} = Par.colOf Ls cur x.val := by
  rw [Finset.card_filter, sum_split _ hj]
  simp only [lam, mem_filter, mem_univ, true_and]
  rw [sum_getD (fun L => if x.val ∈ L then 1 else 0) Ls [cur], getD_mid]
  simp only [getD_late, List.not_mem_nil, if_false, sum_const_zero, add_zero, Par.colOf, countP_eq_sum]
end ClauseBound.ParityChecks.Num
