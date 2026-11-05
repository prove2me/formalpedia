-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.all_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:56.991396+00:00
-- url     : https://prove2.me/submissions/480dbc32-f98c-48a8-b24f-de7c0fe63095

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {Ls : List Chk} {cur : Chk} {e : ℕ} (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) :
    ∀ L ∈ Ls ++ [cur], ChkOK q.m L := by
  intro L hLm
  rcases List.mem_append.1 hLm with h | h
  · exact hL L h
  · rw [List.mem_singleton.1 h]
    exact ⟨hc.1, fun x hx => lt_of_lt_of_le (hc.2 x hx) he⟩
end ClauseBound.ParityChecks.Num
