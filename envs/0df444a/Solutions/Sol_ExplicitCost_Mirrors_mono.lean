-- Prove2me | solution 1 for ExplicitCost.Mirrors.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:19:18.964113+00:00
-- url     : https://prove2.me/submissions/a8609a7e-6788-4f62-821b-c53c00ed7583

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d d' : ℕ} (h : Mirrors M M' w d) (hd : d ≤ d') : Mirrors M M' w d' := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ, { h with size := fun s => (h.size s).trans (Nat.add_le_add_left hd _) }⟩
end Mirrors
end ExplicitCost
