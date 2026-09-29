-- Prove2me | solution 1 for FamousTheorems.acf_complete_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:54:00.572654+00:00
-- url     : https://prove2.me/submissions/48b5f68a-a9de-4aaf-ac9f-1346f8ef90d6

import Mathlib

theorem solution {p : ℕ} (hp : p.Prime ∨ p = 0) : (FirstOrder.Language.Theory.ACF p).IsComplete :=
  FirstOrder.Field.ACF_isComplete hp
