-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.sum_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:28.817059+00:00
-- url     : https://prove2.me/submissions/77eb7b71-bfc6-443c-8617-1efe2f68257b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_sum_powerset_sig
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_two
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_prod_mul_prod

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) :
    ∑ S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂)), ∏ j, fac J₁ J₂ j (S j) = (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) := by
  rw [← prod_univ_sum, prod_mul_prod hJ]
  refine prod_congr rfl fun j _ => ?_
  unfold dom fac
  by_cases h1 : j ∈ J₁
  · simp only [if_pos h1, if_pos (mem_union_left J₂ h1)]
    exact sum_powerset_sig _
  · by_cases h2 : j ∈ J₂
    · simp only [if_neg h1, if_pos h2, if_pos (mem_union_right J₁ h2)]
      exact sum_powerset_neg_two _
    · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
      simp only [if_neg h1, if_neg h2, if_neg h3, sum_singleton]
end ClauseBound.ParityChecks.StepOne
