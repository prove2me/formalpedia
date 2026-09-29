-- Prove2me | solution 1 for FamousTheorems.pell_eq_pell
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:36:47.283569+00:00
-- url     : https://prove2.me/submissions/4c16c74c-02bd-4779-bd7c-6f6f2c362385

import Mathlib

theorem solution : ∀ {a : ℕ} (a1 : 1 < a) {x y : ℕ}, x * x - (a * a - 1) * y * y = 1 →
    ∃ n, x = Pell.xn a1 n ∧ y = Pell.yn a1 n := Pell.eq_pell
