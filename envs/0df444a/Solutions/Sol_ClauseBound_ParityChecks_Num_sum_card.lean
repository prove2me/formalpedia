-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:39.913812+00:00
-- url     : https://prove2.me/submissions/338eef7e-0701-486e-86fc-e52ac7b8d2c2

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
import Theorems.Thm_ClauseBound_ParityChecks_card_lam

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {Ls : List Chk} {cur : Chk} (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (hj : Ls.length < q.r) :
    ∑ j' ∈ range q.r, #(lam q.m (Ls ++ [cur]) j') = (Ls.map List.length).sum + cur.length := by
  simp_rw [card_lam q hall]
  rw [sum_split _ hj, sum_getD List.length Ls [cur], getD_mid]
  simp only [getD_late, List.length_nil, sum_const_zero, add_zero]
end ClauseBound.ParityChecks.Num
