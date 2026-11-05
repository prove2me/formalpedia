-- Prove2me | solution 1 for Coding.pairwise_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:59:26.200213+00:00
-- url     : https://prove2.me/submissions/19d052ce-5cfe-4002-a1e7-1e49246493ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
namespace Coding
theorem _root_.solution {α β : Type} {r₁ : α → α → Prop} {r₂ : β → β → Prop} {l₁ : List α} {l₂ : List β} (h₁ : l₁.Pairwise r₁) (h₂ : l₂.Pairwise r₂) :
    (l₁ ×ˢ l₂).Pairwise fun p q => r₁ p.1 q.1 ∨ (p.1 = q.1 ∧ r₂ p.2 q.2) := by
  induction l₁ with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    rw [List.product_cons, List.pairwise_append]
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 h₁
    refine ⟨List.pairwise_map.2 (h₂.imp fun h => Or.inr ⟨rfl, h⟩), ih hl, ?_⟩
    intro p hp q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
    obtain ⟨q1, q2⟩ := q
    exact Or.inl (hx q1 (List.mem_product.1 hq).1)
end Coding
