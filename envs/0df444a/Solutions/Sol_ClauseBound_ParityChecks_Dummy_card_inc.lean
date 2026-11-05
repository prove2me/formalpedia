-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.card_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:33.127933+00:00
-- url     : https://prove2.me/submissions/787930b8-4c95-447b-964f-9e3bd177870d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) :
    #(inc V r Λ J₁ J₂ ξ y) = ∑ j : Fin r, if (j ∈ J₁ ∧ y j = true) ∨ j ∈ J₂ then #(Λ j ∩ V ξ) else 0 := by
  rw [inc, card_filter, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun j _ => ?_
  by_cases hc : (j ∈ J₁ ∧ y j = true) ∨ j ∈ J₂
  · simp only [hc, and_true, if_true]
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  · simp only [hc, and_false, if_false, sum_const_zero]
end ClauseBound.ParityChecks.Dummy
