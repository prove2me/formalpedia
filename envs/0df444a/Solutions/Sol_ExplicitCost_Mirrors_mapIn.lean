-- Prove2me | solution 1 for ExplicitCost.Mirrors.mapIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:19:32.040763+00:00
-- url     : https://prove2.me/submissions/a3cee803-c72b-422f-a722-644ca98b0edc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution {M : QueryMachine Q A β γ} {M' : QueryMachine Q A β' γ} {w₂ : β → β'} {d : ℕ} (h : Mirrors M M' w₂ d) {g : α → β} {g' : α' → β'} {w : α → α'} (hg : ∀ a, g' (w a) = w₂ (g a)) :
    Mirrors (QueryMachine.mapIn g M) (QueryMachine.mapIn g' M') w d := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ,
    { init := fun a => by
        change M'.init (g' (w a)) = φ (M.init (g a))
        rw [hg, h.init]
      out := h.out, ask := h.ask, step := h.step, resume := h.resume, size := h.size }⟩
end Mirrors
end ExplicitCost
