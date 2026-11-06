-- Prove2me | solution 1 for ExplicitCost.Mirrors.within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:28.765226+00:00
-- url     : https://prove2.me/submissions/99f0ca4f-a71a-48ef-be79-e46bb1ea0278

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Mirrors_runs

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) {O : Q → Option A} {p : Q → ℕ} {a : α} {T S : ℕ} {b : β}
    (r : M.Within O p a T S b) : M'.Within O p (w a) T (S + d) b := by
  obtain ⟨own, L, r, hle⟩ := r
  exact ⟨own, L, h.runs r, hle⟩
end Mirrors
end ExplicitCost
