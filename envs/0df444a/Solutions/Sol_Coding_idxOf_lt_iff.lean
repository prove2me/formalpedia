-- Prove2me | solution 1 for Coding.idxOf_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:52.102191+00:00
-- url     : https://prove2.me/submissions/9a6541a4-4cc1-424e-891e-da95d48c7b80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_idxOf
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.idxOf



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
namespace Coding
theorem _root_.solution {α : Type} [BEq α] [LawfulBEq α] {f : α → ℕ} {l : List α} (hl : l.Pairwise fun x y => f x < f y) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    l.idxOf x < l.idxOf y ↔ f x < f y := by
  have key : ∀ {x y : α}, x ∈ l → y ∈ l → l.idxOf x < l.idxOf y → f x < f y := by
    intro x y hx hy h
    have hx' := List.idxOf_lt_length_of_mem hx
    have hy' := List.idxOf_lt_length_of_mem hy
    have h2 := List.pairwise_iff_getElem.1 hl _ _ hx' hy' h
    rwa [List.getElem_idxOf hx', List.getElem_idxOf hy'] at h2
  refine ⟨key hx hy, fun h => ?_⟩
  by_contra hn
  rcases Nat.lt_or_eq_of_le (not_lt.1 hn) with h' | h'
  · have := key hy hx h'
    omega
  · have e : y = x := (List.idxOf_inj hy).1 h'
    subst e
    omega
end Coding
