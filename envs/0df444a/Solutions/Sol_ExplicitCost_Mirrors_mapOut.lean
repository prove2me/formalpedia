-- Prove2me | solution 1 for ExplicitCost.Mirrors.mapOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:53.211948+00:00
-- url     : https://prove2.me/submissions/db4a08cc-65c2-40b7-b860-2afadedbe708

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
theorem _root_.solution {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) (g : β → γ) :
    Mirrors (QueryMachine.mapOut M g) (QueryMachine.mapOut M' g) w d := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ,
    { init := h.init
      out := fun s => congrArg (Option.map g) (h.out s)
      ask := h.ask, step := h.step, resume := h.resume, size := h.size }⟩
end Mirrors
end ExplicitCost
