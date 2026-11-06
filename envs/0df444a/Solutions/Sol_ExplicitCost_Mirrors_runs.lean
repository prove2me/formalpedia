-- Prove2me | solution 1 for ExplicitCost.Mirrors.runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:26:20.241065+00:00
-- url     : https://prove2.me/submissions/358340f6-1c03-4aed-aa54-20ba45827122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Follows_reaches

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) {O : Q → Option A} {a : α} {own S : ℕ} {L : List Q} {b : β}
    (r : M.Runs O a own L S b) : M'.Runs O (w a) own L (S + d) b := by
  obtain ⟨φ, h⟩ := h
  unfold QueryMachine.Runs
  rw [h.init]
  exact h.reaches r
end Mirrors
end ExplicitCost
