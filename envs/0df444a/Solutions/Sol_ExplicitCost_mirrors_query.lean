-- Prove2me | solution 1 for ExplicitCost.mirrors_query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:24:17.518839+00:00
-- url     : https://prove2.me/submissions/e7dca97f-a561-42f4-b138-c60fec9d7f4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
theorem _root_.solution [HasSize α] [HasSize α'] [HasSize A] {h : α → Q} {h' : α' → Q} {w : α → α'} {d : ℕ} (hh : ∀ a, h' (w a) = h a) (hw : ∀ a, size (w a) ≤ size a + d) :
    Mirrors (QueryMachine.query h : QueryMachine Q A α A) (QueryMachine.query h') w d :=
  ⟨(Sum.map w id : α ⊕ A → α' ⊕ A),
    { init := fun _ => rfl
      out := fun s => by rcases s with a | v <;> rfl
      ask := fun s => by
        rcases s with a | v
        · exact congrArg some (hh a)
        · rfl
      step := fun _ => rfl
      resume := fun _ _ => rfl
      size := fun s => by
        rcases s with a | v
        · change size (w a) + 1 ≤ size a + 1 + d
          have := hw a
          omega
        · change size v + 1 ≤ size v + 1 + d
          omega }⟩
end ExplicitCost
