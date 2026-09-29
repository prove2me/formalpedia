-- Prove2me | solution 1 for FamousTheorems.freiman_three_halves_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:58:35.204285+00:00
-- url     : https://prove2.me/submissions/0affb8c8-445e-412c-9add-61fd1afa94e2

import Mathlib

open Pointwise

theorem solution {G : Type*} [Group G] [DecidableEq G] {A : Finset G}
    (h : ((A * A).card : ℚ) < 3 / 2 * A.card) :
    ∃ (H : Subgroup G) (_ : Fintype H), (Fintype.card H : ℚ) < 3 / 2 * A.card ∧
      ∀ a ∈ A, (A : Set G) ⊆ a • (H : Set G) ∧ a • (H : Set G) = MulOpposite.op a • (H : Set G) :=
  Finset.doubling_lt_three_halves h
