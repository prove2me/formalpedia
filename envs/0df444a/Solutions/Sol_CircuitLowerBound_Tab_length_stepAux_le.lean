-- Prove2me | solution 1 for CircuitLowerBound.Tab.length_stepAux_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:25.097211+00:00
-- url     : https://prove2.me/submissions/9e0774c5-5604-402d-aa88-252ee3342adc

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
theorem _root_.solution (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A : ∀ k, List (Γ k)) (k : K),
    ((TM2.stepAux q v A).stk k).length ≤ (A k).length + ops q := by
  induction q with
  | push k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | peek k f q ih => intro v A k'; simp only [TM2.stepAux]; exact (ih _ _ k').trans (by simp [ops])
  | pop k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | load a q ih => intro v A k'; simp only [TM2.stepAux]; exact ih _ _ k'
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v A k'
    simp only [TM2.stepAux]
    cases f v
    · exact (ih₂ v A k').trans (by simp [ops])
    · exact (ih₁ v A k').trans (by simp [ops])
  | goto f => intro v A k'; simp [TM2.stepAux, ops]
  | halt => intro v A k'; simp [TM2.stepAux, ops]
end CircuitLowerBound.Tab
