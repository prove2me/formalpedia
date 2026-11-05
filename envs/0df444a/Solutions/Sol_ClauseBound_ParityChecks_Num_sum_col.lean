-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:34.948649+00:00
-- url     : https://prove2.me/submissions/c6b331a2-7297-41f8-91b5-7e9c80ea2010

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_list_sum_range
import Theorems.Thm_ClauseBound_ParityChecks_Num_card_col
import Theorems.Thm_ClauseBound_ParityChecks_Num_sub_undCol

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    ∑ x : Fin q.m, 2 ^ #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} * q.nb ^ (q.r - undCol q.r Ls.length (Dset q.m e) x) *
      (q.nb + 1) ^ (q.r - (q.r - undCol q.r Ls.length (Dset q.m e) x)) = q.numC Ls cur e := by
  simp_rw [card_col cur hj, sub_undCol hj]
  unfold Par.numC
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
end ClauseBound.ParityChecks.Num
