-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.neg_one_pow_card_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:16.444415+00:00
-- url     : https://prove2.me/submissions/f15305e5-df1e-4cbe-a970-fa31aa715e3c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_card_inc

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) :
    (-1 : ℤ) ^ #(inc V r Λ J₁ J₂ ξ y) = ∏ j, fac V r Λ J₁ J₂ ξ j (y j) := by
  rw [card_inc, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun j _ => ?_
  unfold fac
  split_ifs
  · rfl
  · exact pow_zero _
end ClauseBound.ParityChecks.Dummy
