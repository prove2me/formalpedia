-- Prove2me | solution 1 for ExplicitCost.bind_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:52:38.529638+00:00
-- url     : https://prove2.me/submissions/620bb1cd-adf8-4248-b3f9-58cb35f88565

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_QueryMachines_stBindRuns


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T T' S S' : ℕ} {b : β} {c : γ} (h : M.Within O w a T S b)
    (h' : N.Within O w (a, b) T' S' c) : (QueryMachine.bind M N).Within O w a (T + 1 + T') (max (size a + S) S' + 1) c :=
  let ⟨own, L, hr, hle⟩ := h
  let ⟨own', L', hr', hle'⟩ := h'
  ⟨own + 1 + own', L ++ L', stBindRuns _ _ _ _ _ M N O a own own' S S' L L' b c hr hr', by rw [List.map_append, List.sum_append]; omega⟩
end ExplicitCost
