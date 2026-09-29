-- Prove2me | solution 1 for FamousTheorems.ade_inequality_classification
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:27:39.372191+00:00
-- url     : https://prove2.me/submissions/77dfe05e-a279-4c00-b85c-972867178ff0

import Mathlib

theorem solution (p q r : ℕ+) : 1 < ADEInequality.sumInv {p, q, r} ↔ ADEInequality.Admissible {p, q, r} :=
  ADEInequality.classification p q r
