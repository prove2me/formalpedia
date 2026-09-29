-- Prove2me | solution 1 for FamousTheorems.first_supplementary_law_qr
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:08:51.408188+00:00
-- url     : https://prove2.me/submissions/466eccc0-47b1-444f-89dc-ff14ed6075df

import Mathlib

theorem solution {p : ℕ} [Fact p.Prime] : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 :=
  ZMod.exists_sq_eq_neg_one_iff
