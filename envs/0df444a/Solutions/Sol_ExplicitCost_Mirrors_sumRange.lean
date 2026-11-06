-- Prove2me | solution 1 for ExplicitCost.Mirrors.sumRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:35:09.619534+00:00
-- url     : https://prove2.me/submissions/055b3cbc-324e-4584-ba0c-1f13a53f1bc8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Mirrors_foldRange
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
theorem _root_.solution [HasSize α] [HasSize α'] {M : QueryMachine Q A (α × ℕ) ℤ} {M' : QueryMachine Q A (α' × ℕ) ℤ} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (hN : ∀ a, N' (w a) = N a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.sumRange N M) (QueryMachine.sumRange N' M') w d :=
  Mirrors.foldRange hM Stepped.addG hN (fun _ => rfl) hw h1
end Mirrors
end ExplicitCost
