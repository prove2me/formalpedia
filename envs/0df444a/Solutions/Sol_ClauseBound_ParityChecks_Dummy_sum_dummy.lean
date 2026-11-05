-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.sum_dummy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:57.317055+00:00
-- url     : https://prove2.me/submissions/33ff345a-84df-4d19-bb82-c4dcd56759d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_powerset_neg_two
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_neg_one_pow_card_inc
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_fac

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) :
    ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset, (-2 : ℤ) ^ #S =
      2 ^ r * ((∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) := by
  simp only [sum_powerset_neg_two, neg_one_pow_card_inc]
  rw [← Fintype.piFinset_univ, ← prod_univ_sum]
  simp only [sum_fac V r Λ J₁ J₂ h ξ]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, Fintype.prod_ite_mem, Fintype.prod_ite_mem]
end ClauseBound.ParityChecks.Dummy
