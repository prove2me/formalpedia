-- Prove2me | solution 2 for FamousTheorems.strong_pigeonhole_principle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:50:09.969385+00:00
-- url     : https://prove2.me/submissions/c6157251-018f-4682-a44e-83c6d8d3eacc

import Mathlib

theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) {n : ℕ}
    (hn : Fintype.card β * n < Fintype.card α) : ∃ y : β, n < (Finset.univ.filter fun x => f x = y).card :=
  Fintype.exists_lt_card_fiber_of_mul_lt_card f hn
