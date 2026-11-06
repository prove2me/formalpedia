-- Prove2me | solution 1 for ExplicitCost.Mirrors.branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:00.817515+00:00
-- url     : https://prove2.me/submissions/bc82060f-4db0-42f7-96e3-fbc4be4f0341

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
namespace Mirrors
theorem _root_.solution {M₁ : QueryMachine Q A α₁ β} {M₁' : QueryMachine Q A α₁' β} {M₂ : QueryMachine Q A α₂ β} {M₂' : QueryMachine Q A α₂' β} {w₁ : α₁ → α₁'} {w₂ : α₂ → α₂'} {d : ℕ}
    (h₁ : Mirrors M₁ M₁' w₁ d) (h₂ : Mirrors M₂ M₂' w₂ d) {sel : α → α₁ ⊕ α₂} {sel' : α' → α₁' ⊕ α₂'} {w : α → α'} (hs : ∀ a, sel' (w a) = Sum.map w₁ w₂ (sel a)) :
    Mirrors (QueryMachine.branch sel M₁ M₂) (QueryMachine.branch sel' M₁' M₂') w d := by
  obtain ⟨φ₁, h₁⟩ := h₁
  obtain ⟨φ₂, h₂⟩ := h₂
  exact ⟨(Sum.map φ₁ φ₂ : M₁.σ ⊕ M₂.σ → M₁'.σ ⊕ M₂'.σ),
    { init := fun a => by
        change (match sel' (w a) with | .inl x => (.inl (M₁'.init x) : M₁'.σ ⊕ M₂'.σ) | .inr y => .inr (M₂'.init y)) =
          Sum.map φ₁ φ₂ (match sel a with | .inl x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ) | .inr y => .inr (M₂.init y))
        rw [hs]
        cases sel a with
        | inl x => exact congrArg Sum.inl (h₁.init x)
        | inr y => exact congrArg Sum.inr (h₂.init y)
      out := fun s => by
        rcases s with s | s
        · exact h₁.out s
        · exact h₂.out s
      ask := fun s => by
        rcases s with s | s
        · exact h₁.ask s
        · exact h₂.ask s
      step := fun s => by
        rcases s with s | s
        · exact congrArg Sum.inl (h₁.step s)
        · exact congrArg Sum.inr (h₂.step s)
      resume := fun s v => by
        rcases s with s | s
        · exact congrArg Sum.inl (h₁.resume s v)
        · exact congrArg Sum.inr (h₂.resume s v)
      size := fun s => by
        rcases s with s | s
        · change size (φ₁ s) + 1 ≤ size s + 1 + d
          have := h₁.size s
          omega
        · change size (φ₂ s) + 1 ≤ size s + 1 + d
          have := h₂.size s
          omega }⟩
end Mirrors
end ExplicitCost
