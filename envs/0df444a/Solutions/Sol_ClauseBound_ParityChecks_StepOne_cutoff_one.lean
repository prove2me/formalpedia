-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.cutoff_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:14:58.747102+00:00
-- url     : https://prove2.me/submissions/7129c7b1-8a64-49bc-b541-b582b4dfda60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_prod_mul_prod
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_sum_all
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_dvd_term

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) {ν M : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + #J₁ ≤ M) :
    (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) ≡
      ∑ S ∈ (Fintype.piFinset (dom A (J₁ ∪ J₂))).filter (fun S => ∑ j, #(S j) ≤ M), (∏ j ∈ J₁, sig #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j)
      [ZMOD 2 ^ ν] := by
  have h1 : ∀ S : Fin r → Finset E, (∏ j ∈ J₁, sig #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j) = ∏ j, fac J₁ J₂ j (S j) := fun S =>
    prod_mul_prod hJ _ _
  simp only [h1]
  rw [← sum_all hJ A, ← sum_filter_add_sum_filter_not (Fintype.piFinset (dom A (J₁ ∪ J₂))) fun S => ∑ j, #(S j) ≤ M]
  refine (Int.modEq_iff_dvd.2 ?_)
  rw [sub_add_cancel_left, dvd_neg]
  refine dvd_sum fun S hS => ?_
  obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
  exact dvd_term A hS1 (by omega)
end ClauseBound.ParityChecks.StepOne
