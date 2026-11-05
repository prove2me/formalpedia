-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.tent_in
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:38.982669+00:00
-- url     : https://prove2.me/submissions/a53e915e-a66b-408d-95c7-ff44cf56091d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_card_putIn_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution {Λ : ℕ → Finset (Fin q.m)} (h : Bd q Λ) (j : ℕ) (x : Fin q.m) : Tent q (putIn j Λ x) where
  inc := by
    have h1 : ∑ j' ∈ range q.r, #(putIn j Λ x j') ≤ ∑ j' ∈ range q.r, #(Λ j') + 1 := by
      refine (sum_le_sum fun j' _ => card_putIn_le Λ j x j').trans ?_
      rw [sum_add_distrib, sum_ite_eq']
      split_ifs <;> omega
    have h2 : ((∑ j' ∈ range q.r, #(putIn j Λ x j') : ℕ) : ℚ) ≤ ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) + 1 := by exact_mod_cast h1
    have := h.inc
    linarith
  row j' hj' := by
    have h1 : (2 : ℚ) ^ #(putIn j Λ x j') ≤ 2 ^ (#(Λ j') + 1) :=
      pow_le_pow_right₀ (by norm_num) ((card_putIn_le Λ j x j').trans (by split_ifs <;> omega))
    have := h.row j' hj'
    rw [pow_succ] at h1
    linarith
  col y := by
    have h0 : #{j' ∈ range q.r | y ∈ putIn j Λ x j'} ≤ #{j' ∈ range q.r | y ∈ Λ j'} + 1 := by
      refine (card_le_card (t := insert j {j' ∈ range q.r | y ∈ Λ j'}) fun j' hj' => ?_).trans (card_insert_le _ _)
      obtain ⟨h1, h2⟩ := mem_filter.1 hj'
      by_cases hjj : j' = j
      · exact mem_insert.2 (Or.inl hjj)
      · rw [putIn, Function.update_of_ne hjj] at h2
        exact mem_insert.2 (Or.inr (mem_filter.2 ⟨h1, h2⟩))
    have h1 : (2 : ℚ) ^ #{j' ∈ range q.r | y ∈ putIn j Λ x j'} ≤ 2 ^ (#{j' ∈ range q.r | y ∈ Λ j'} + 1) :=
      pow_le_pow_right₀ (by norm_num) h0
    have := h.col y
    rw [pow_succ] at h1
    linarith
end ClauseBound.ParityChecks.Run
