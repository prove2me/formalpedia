-- Prove2me | solution 1 for ClauseBound.ParityChecks.isState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:32.543192+00:00
-- url     : https://prove2.me/submissions/f4484759-5e58-43b8-bdf3-be9f971a2264

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_mid
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_late

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
namespace ClauseBound.ParityChecks
theorem _root_.solution {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur) :
    IsState q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
  refine ⟨hj, fun j' hj' => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j' = Ls.length + 1 + i := ⟨j' - (Ls.length + 1), by omega⟩
    unfold lam
    rw [Num.getD_late]
    simp
  · rw [Finset.disjoint_left]
    intro x hx hx'
    unfold lam at hx
    rw [Num.getD_mid] at hx
    have h1 := hc.2 _ (Finset.mem_filter.1 hx).2
    have h2 := (Finset.mem_filter.1 hx').2
    omega
end ClauseBound.ParityChecks
