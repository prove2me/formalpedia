-- Prove2me | solution 1 for ExplicitCost.Mirrors.foldWhile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:05.999098+00:00
-- url     : https://prove2.me/submissions/01449de8-4868-45d7-bb74-d9b46eead048

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
theorem _root_.solution [HasSize τ] [HasSize τ'] [HasSize γ] {M : QueryMachine Q A τ β} {M' : QueryMachine Q A τ' β} {wt : τ → τ'} {d₁ dw d : ℕ} (hM : Mirrors M M' wt d₁)
    {start : α → Option τ} {start' : α' → Option τ'} {nxt : τ → Option τ} {nxt' : τ' → Option τ'} {g : γ → τ → β → γ} {g' : γ → τ' → β → γ} {c₀ : α → γ} {c₀' : α' → γ} {w : α → α'}
    (hs : ∀ a, start' (w a) = (start a).map wt) (hn : ∀ t, nxt' (wt t) = (nxt t).map wt) (hg : ∀ c t b, g' c (wt t) b = g c t b) (hc : ∀ a, c₀' (w a) = c₀ a)
    (hw : ∀ t, size (wt t) ≤ size t + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldWhile start nxt M g c₀) (QueryMachine.foldWhile start' nxt' M' g' c₀') w d := by
  obtain ⟨φ, hM⟩ := hM
  have key : ∀ (c : γ) (o : Option τ), Stepped.foldGo M'.toStepped c (o.map wt) =
      (Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id : (τ × γ × M.σ) ⊕ γ → (τ' × γ × M'.σ) ⊕ γ) (Stepped.foldGo M.toStepped c o) := by
    intro c o
    cases o with
    | none => rfl
    | some x => exact congrArg (fun s => (Sum.inl (wt x, c, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.init x)
  exact ⟨(Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id : (τ × γ × M.σ) ⊕ γ → (τ' × γ × M'.σ) ⊕ γ),
    { init := fun a => by
        change Stepped.foldGo M'.toStepped (c₀' (w a)) (start' (w a)) = _
        rw [hc, hs]
        exact key _ _
      out := fun s => by rcases s with p | c <;> rfl
      ask := fun s => by
        rcases s with p | c
        · change (match M'.out (φ p.2.2) with | some _ => none | none => M'.ask (φ p.2.2)) = (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
          rw [hM.out, hM.ask]
        · rfl
      step := fun s => by
        rcases s with p | c
        · change (match M'.out (φ p.2.2) with | some b => Stepped.foldGo M'.toStepped (g' p.2.1 (wt p.1) b) (nxt' (wt p.1)) | none => .inl (wt p.1, p.2.1, M'.step (φ p.2.2))) =
            Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id
              (match M.out p.2.2 with | some b => Stepped.foldGo M.toStepped (g p.2.1 p.1 b) (nxt p.1) | none => .inl (p.1, p.2.1, M.step p.2.2))
          rw [hM.out]
          cases M.out p.2.2 with
          | none => exact congrArg (fun s => (Sum.inl (wt p.1, p.2.1, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.step p.2.2)
          | some b =>
            change Stepped.foldGo M'.toStepped (g' p.2.1 (wt p.1) b) (nxt' (wt p.1)) = _
            rw [hg, hn]
            exact key _ _
        · rfl
      resume := fun s v => by
        rcases s with p | c
        · exact congrArg (fun s => (Sum.inl (wt p.1, p.2.1, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.resume p.2.2 v)
        · rfl
      size := fun s => by
        rcases s with p | c
        · change size (wt p.1) + (size p.2.1 + size (φ p.2.2)) + 1 ≤ size p.1 + (size p.2.1 + size p.2.2) + 1 + d
          have := hw p.1
          have := hM.size p.2.2
          omega
        · change size c + 1 ≤ size c + 1 + d
          omega }⟩
end Mirrors
end ExplicitCost
