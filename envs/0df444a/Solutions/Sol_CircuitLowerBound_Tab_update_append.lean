-- Prove2me | solution 1 for CircuitLowerBound.Tab.update_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:11.450096+00:00
-- url     : https://prove2.me/submissions/c9c45391-ce3f-4c63-ba6f-3858778993ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
namespace CircuitLowerBound.Tab
theorem _root_.solution (A R : ∀ k, List (Γ k)) (k : K) (w : List (Γ k)) :
    Function.update (fun k => A k ++ R k) k (w ++ R k) = fun k' => Function.update A k w k' ++ R k' := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]
end CircuitLowerBound.Tab
