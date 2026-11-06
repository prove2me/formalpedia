-- Prove2me | solution 1 for ExplicitCost.Mirrors.foldRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:27.944342+00:00
-- url     : https://prove2.me/submissions/8cd350a3-5e9c-4a9e-a5b4-9b36c386fce7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Mirrors_foldWhile
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
theorem _root_.solution [HasSize α] [HasSize α'] [HasSize γ] {M : QueryMachine Q A (α × ℕ) β} {M' : QueryMachine Q A (α' × ℕ) β} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (g : γ → ℕ → β → γ) {c₀ : α → γ} {c₀' : α' → γ} (hN : ∀ a, N' (w a) = N a) (hc : ∀ a, c₀' (w a) = c₀ a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldRange N M g c₀) (QueryMachine.foldRange N' M' g c₀') w d :=
  Mirrors.foldWhile hM
    (fun a => by
      unfold Stepped.rangeStart
      rw [hN a]
      split <;> rfl)
    (fun t => by
      unfold Stepped.rangeNext
      change (if t.2 + 1 < N' (w t.1) then some (w t.1, t.2 + 1) else none) = _
      rw [hN t.1]
      split <;> rfl)
    (fun _ _ _ => rfl) hc
    (fun t => by
      change size (w t.1) + size t.2 ≤ size t.1 + size t.2 + dw
      have := hw t.1
      omega) h1
end Mirrors
end ExplicitCost
