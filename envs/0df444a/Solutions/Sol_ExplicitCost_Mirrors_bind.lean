-- Prove2me | solution 1 for ExplicitCost.Mirrors.bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:01.840313+00:00
-- url     : https://prove2.me/submissions/27510e2e-72c9-4701-bff5-bd837eda9299

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
theorem _root_.solution [HasSize α] [HasSize α'] {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {N : QueryMachine Q A (α × β) γ} {N' : QueryMachine Q A (α' × β) γ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' (Prod.map w id) d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.bind M N) (QueryMachine.bind M' N') w d := by
  obtain ⟨φ, hM⟩ := hM
  obtain ⟨ψ, hN⟩ := hN
  exact ⟨(Sum.map (Prod.map w φ) ψ : (α × M.σ) ⊕ N.σ → (α' × M'.σ) ⊕ N'.σ),
    { init := fun a => congrArg (fun s => (Sum.inl (w a, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.init a)
      out := fun s => by
        rcases s with p | s
        · rfl
        · exact hN.out s
      ask := fun s => by
        rcases s with p | s
        · change (match M'.out (φ p.2) with | some _ => none | none => M'.ask (φ p.2)) = (match M.out p.2 with | some _ => none | none => M.ask p.2)
          rw [hM.out, hM.ask]
        · exact hN.ask s
      step := fun s => by
        rcases s with p | s
        · change (match M'.out (φ p.2) with | some b => (.inr (N'.init (w p.1, b)) : (α' × M'.σ) ⊕ N'.σ) | none => .inl (w p.1, M'.step (φ p.2))) =
            Sum.map (Prod.map w φ) ψ (match M.out p.2 with | some b => (.inr (N.init (p.1, b)) : (α × M.σ) ⊕ N.σ) | none => .inl (p.1, M.step p.2))
          rw [hM.out]
          cases M.out p.2 with
          | none => exact congrArg (fun s => (Sum.inl (w p.1, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.step p.2)
          | some b => exact congrArg Sum.inr (hN.init (p.1, b))
        · exact congrArg Sum.inr (hN.step s)
      resume := fun s v => by
        rcases s with p | s
        · exact congrArg (fun s => (Sum.inl (w p.1, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.resume p.2 v)
        · exact congrArg Sum.inr (hN.resume s v)
      size := fun s => by
        rcases s with p | s
        · change size (w p.1) + size (φ p.2) + 1 ≤ size p.1 + size p.2 + 1 + d
          have := hw p.1
          have := hM.size p.2
          omega
        · change size (ψ s) + 1 ≤ size s + 1 + d
          have := hN.size s
          omega }⟩
end Mirrors
end ExplicitCost
