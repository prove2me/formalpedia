-- Prove2me | solution 1 for ClauseBound.Group.Grouping.card_colour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:07.781738+00:00
-- url     : https://prove2.me/submissions/4e61efe8-df51-4830-a2c5-e056eed71a12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
namespace ClauseBound.Group.Grouping
theorem _root_.solution {V : Type} [Fintype V] [DecidableEq V] (A B : Finset V) (h : Disjoint A B) (y : Bool × Bool) :
    #{x | (decide (x ∈ A), decide (x ∈ B)) = y} =
      if y.1 = true then (if y.2 = true then 0 else #A) else (if y.2 = true then #B else Fintype.card V - (#A + #B)) := by
  obtain ⟨y1, y2⟩ := y
  cases y1 <;> cases y2 <;> simp only [Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq_true, if_false, if_true]
  · rw [← card_union_of_disjoint h, ← card_compl]
    congr 1
    ext x; simp
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hx => hx.2, fun hx => ⟨fun hA => disjoint_left.1 h hA hx, hx⟩⟩
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, disjoint_left.1 h hx⟩⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun x _ hx => disjoint_left.1 h hx.1 hx.2
end ClauseBound.Group.Grouping
