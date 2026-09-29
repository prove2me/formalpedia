-- Prove2me | solution 1 for FamousTheorems.dvd_iff_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:47.942356+00:00
-- url     : https://prove2.me/submissions/88266eb7-6c4b-45c3-b3c9-1358dd75bead

import Mathlib

theorem solution : ∀ {R : Type*} {a : R} [CommRing R] {p : Polynomial R},
    (Polynomial.X - Polynomial.C a) ∣ p ↔ p.IsRoot a :=
  Polynomial.dvd_iff_isRoot
