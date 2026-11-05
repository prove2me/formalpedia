-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.cutoff_dummy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:23.144957+00:00
-- url     : https://prove2.me/submissions/601b31d8-0472-4ca2-af78-6fd86b4e8492

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_dummy
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_neg_two_pow_modEq

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (f : X → ℤ) (M : ℕ) :
    2 ^ r * (∑ ξ, f ξ * (∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) ≡
      ∑ ξ, f ξ * ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S [ZMOD 2 ^ (M + 1)] := by
  rw [mul_sum]
  refine Int.ModEq.sum fun ξ _ => ?_
  have e : 2 ^ r * (f ξ * (∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) =
      f ξ * ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset, (-2 : ℤ) ^ #S := by
    rw [sum_dummy V r Λ J₁ J₂ h ξ]
    ring
  rw [e]
  refine Int.ModEq.mul_left _ (Int.ModEq.sum fun y _ => ?_)
  rw [sum_filter]
  exact Int.ModEq.sum fun S _ => neg_two_pow_modEq
end ClauseBound.ParityChecks.Dummy
