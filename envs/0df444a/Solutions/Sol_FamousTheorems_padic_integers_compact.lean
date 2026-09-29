-- Prove2me | solution 1 for FamousTheorems.padic_integers_compact
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:30:57.437851+00:00
-- url     : https://prove2.me/submissions/34837e27-714f-4e54-9927-0cb59b386e1d

import Mathlib

theorem solution (p : ℕ) [Fact p.Prime] : CompactSpace (PadicInt p) :=
  PadicInt.compactSpace p
