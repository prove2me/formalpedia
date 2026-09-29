-- Prove2me | solution 1 for FamousTheorems.chicken_mcnugget_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:01:35.176032+00:00
-- url     : https://prove2.me/submissions/d2a0baed-97cb-4acf-bb12-ecd3a0d4e60d

import Mathlib

theorem solution {m n : ℕ} (hmn : m.Coprime n) (hm : 1 < m) (hn : 1 < n) : FrobeniusNumber (m * n - m - n) ({m, n} : Set ℕ) :=
  frobeniusNumber_pair hmn hm hn
