-- Prove2me | solution 1 for FamousTheorems.stars_and_bars_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:45:48.428872+00:00
-- url     : https://prove2.me/submissions/cfec6538-34e6-4d94-b8a3-b32a66f1dfba

import Mathlib

theorem solution (α : Type*) (k : ℕ) [Fintype α] [DecidableEq α] :
    Fintype.card (Sym α k) = (Fintype.card α).multichoose k :=
  Sym.card_sym_eq_multichoose α k
