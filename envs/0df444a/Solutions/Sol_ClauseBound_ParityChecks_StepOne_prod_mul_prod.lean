-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.prod_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:03.680101+00:00
-- url     : https://prove2.me/submissions/59a767a7-0898-433f-83ae-32e99b1c48bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (a b : Fin r → ℤ) :
    (∏ j ∈ J₁, a j) * ∏ j ∈ J₂, b j = ∏ j, if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1 := by
  have h : ∀ j : Fin r, (if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1) = (if j ∈ J₁ then a j else 1) * if j ∈ J₂ then b j else 1 := by
    intro j
    by_cases h1 : j ∈ J₁
    · rw [if_pos h1, if_pos h1, if_neg (disjoint_left.1 hJ h1), mul_one]
    · rw [if_neg h1, if_neg h1, one_mul]
  simp only [h]
  rw [prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter]
end ClauseBound.ParityChecks.StepOne
