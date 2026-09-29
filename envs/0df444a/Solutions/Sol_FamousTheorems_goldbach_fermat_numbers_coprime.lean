-- Prove2me | solution 1 for FamousTheorems.goldbach_fermat_numbers_coprime
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:15:58.967892+00:00
-- url     : https://prove2.me/submissions/7edf1f1c-b929-4503-ba2c-98916334fc3f

import Mathlib

theorem solution {m n : ℕ} (h : m ≠ n) :
    Nat.Coprime (Nat.fermatNumber m) (Nat.fermatNumber n) :=
  Nat.coprime_fermatNumber_fermatNumber h
