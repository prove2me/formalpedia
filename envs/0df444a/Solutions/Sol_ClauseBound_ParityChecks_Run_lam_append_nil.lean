-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.lam_append_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:47.594097+00:00
-- url     : https://prove2.me/submissions/4536a77e-2742-43e5-aab8-16b415263afc

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
theorem _root_.solution (Ls : List Chk) : lam q.m (Ls ++ [[]]) = lam q.m Ls := by
  funext j
  unfold lam
  by_cases hj : j = Ls.length
  · rw [hj, getD_append_self, List.getD_eq_default _ _ le_rfl]
  · rw [getD_append_ne _ _ hj]
end ClauseBound.ParityChecks.Run
