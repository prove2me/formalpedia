-- Prove2me | solution 1 for FamousTheorems.borel_isomorphism_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:46:02.602783+00:00
-- url     : https://prove2.me/submissions/34dce662-9221-4904-8b8e-74a70cf8fae1

import Mathlib

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [StandardBorelSpace β]
    (hα : ¬Countable α) (hβ : ¬Countable β) :
    Nonempty (MeasurableEquiv α β) :=
  ⟨PolishSpace.measurableEquivOfNotCountable hα hβ⟩
