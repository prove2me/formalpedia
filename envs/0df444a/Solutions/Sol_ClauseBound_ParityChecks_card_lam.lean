-- Prove2me | solution 1 for ClauseBound.ParityChecks.card_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:00:09.491127+00:00
-- url     : https://prove2.me/submissions/1ae6be8d-daca-41bb-a2cc-7ff1d9b1534a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_card_filter_mem

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
namespace ClauseBound.ParityChecks
theorem _root_.solution {Ls : List Chk} (hL : ∀ L ∈ Ls, ChkOK q.m L) (j : ℕ) : #(lam q.m Ls j) = (Ls.getD j []).length := by
  unfold lam
  rcases Nat.lt_or_ge j Ls.length with h | h
  · have hmem : Ls.getD j [] ∈ Ls := by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
    exact Num.card_filter_mem (hL _ hmem).1 (hL _ hmem).2
  · rw [List.getD_eq_default _ _ h]; simp
end ClauseBound.ParityChecks
