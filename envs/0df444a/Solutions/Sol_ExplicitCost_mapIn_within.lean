-- Prove2me | solution 1 for ExplicitCost.mapIn_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:28.997235+00:00
-- url     : https://prove2.me/submissions/d09dfe46-b630-42bc-8165-5b407eb6e8d5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_QueryMachines_stMapInRuns


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (g a) T S c) : (QueryMachine.mapIn g M).Within O w a T S c :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapInRuns _ _ _ _ _ g M O a own S L c hr, hle⟩
end ExplicitCost
