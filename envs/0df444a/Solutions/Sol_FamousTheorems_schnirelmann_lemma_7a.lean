-- Prove2me | solution 1 for FamousTheorems.schnirelmann_lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:13:50.980985+00:00
-- url     : https://prove2.me/submissions/7ff79921-58db-4f84-8b10-129ec5d64a59

import Mathlib

open Pointwise

theorem solution {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) : A + B = Set.univ :=
  add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity hA hB h
