-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.lam_putIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:48.605829+00:00
-- url     : https://prove2.me/submissions/a077fe7e-21a4-422e-829b-a24359eb0027

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_getD_append_self
import Theorems.Thm_ClauseBound_ParityChecks_Run_getD_append_ne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (Ls : List Chk) (cur : Chk) {e : ℕ} (he : e < q.m) :
    lam q.m (Ls ++ [cur ++ [e]]) = putIn Ls.length (lam q.m (Ls ++ [cur])) ⟨e, he⟩ := by
  funext j
  unfold putIn lam
  by_cases hj : j = Ls.length
  · rw [hj, Function.update_self, getD_append_self, getD_append_self]
    ext x
    simp only [mem_filter, mem_univ, true_and, List.mem_append, List.mem_singleton, mem_insert, Fin.ext_iff]
    tauto
  · rw [Function.update_of_ne hj, getD_append_ne _ _ hj, getD_append_ne _ _ hj]
end ClauseBound.ParityChecks.Run
