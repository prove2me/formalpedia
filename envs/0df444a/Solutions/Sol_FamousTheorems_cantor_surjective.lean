-- Prove2me | solution 1 for FamousTheorems.cantor_surjective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.687225+00:00
-- url     : https://prove2.me/submissions/1e754a00-082f-4c05-b616-05109ea5bdf1

import Mathlib

theorem solution : ∀ {α : Type*} (f : α → Set α), ¬ Function.Surjective f :=
  Function.cantor_surjective
