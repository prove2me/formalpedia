-- Prove2me | solution 1 for FamousTheorems.strong_pigeonhole_principle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:48:13.953743+00:00
-- url     : https://prove2.me/submissions/85c8da4f-c7ff-46fa-a423-799ad81e3c7f

import Mathlib

theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) {n : ℕ}
    (hn : Fintype.card β * n < Fintype.card α) : ∃ y : β, n < (Finset.univ.filter fun x => f x = y).card :=
  Fintype.exists_lt_card_fiber_of_mul_lt_card f hn
