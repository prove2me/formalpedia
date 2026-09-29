-- Prove2me | solution 1 for FamousTheorems.pythagorean_triple_classification
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:36:47.326108+00:00
-- url     : https://prove2.me/submissions/349f6639-9ec6-446d-a98f-bad2af1fa956

import Mathlib

theorem solution : ∀ {x y z : ℤ}, PythagoreanTriple x y z ↔
    ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) :=
  PythagoreanTriple.classification
