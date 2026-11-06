-- Prove2me | solution 1 for ExplicitCost.mapOut_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:02.035303+00:00
-- url     : https://prove2.me/submissions/db1a7a5e-f5df-4d0d-9bbe-06b1f8733cbd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_QueryMachines_stMapOutRuns


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (h : M.Within O w a T S b) : (QueryMachine.mapOut M g).Within O w a T S (g b) :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapOutRuns _ _ _ _ _ M g O a own S L b hr, hle⟩
end ExplicitCost
