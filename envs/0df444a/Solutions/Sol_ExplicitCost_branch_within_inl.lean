-- Prove2me | solution 1 for ExplicitCost.branch_within_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:52:25.257521+00:00
-- url     : https://prove2.me/submissions/eea490da-9985-4317-95a7-5ce572f919fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_QueryMachines_stBranchRuns


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {w : Q → ℕ} {a : α} {x : α₁} {T S : ℕ} {b : β} (hs : sel a = .inl x)
    (h : M₁.Within O w x T S b) : (QueryMachine.branch sel M₁ M₂).Within O w a T (S + 1) b :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, (stBranchRuns _ _ _ _ _ _ sel M₁ M₂ O a own S L b).1 x hs hr, hle⟩
end ExplicitCost
