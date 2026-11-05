-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.sum_fac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:37.420058+00:00
-- url     : https://prove2.me/submissions/c8f6d7d9-40b0-4aa4-842a-8e89062c9c76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_one_add_neg_one_pow

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X] [Fintype E]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) (j : Fin r) :
    ∑ b : Bool, fac V r Λ J₁ J₂ ξ j b =
      2 * ((if j ∈ J₁ then ev #(Λ j ∩ V ξ) else 1) * if j ∈ J₂ then (-1 : ℤ) ^ #(Λ j ∩ V ξ) else 1) := by
  rw [Fintype.sum_bool]
  unfold fac
  by_cases h1 : j ∈ J₁
  · have h2 : j ∉ J₂ := disjoint_left.1 h h1
    simp only [h1, h2, true_and, or_false, if_true, if_false, Bool.false_eq_true, mul_one]
    exact one_add_neg_one_pow _
  · by_cases h2 : j ∈ J₂
    · simp only [h1, h2, false_and, or_true, if_true, if_false, one_mul]
      ring
    · simp only [h1, h2, false_and, or_false, if_false, mul_one]
      norm_num
end ClauseBound.ParityChecks.Dummy
