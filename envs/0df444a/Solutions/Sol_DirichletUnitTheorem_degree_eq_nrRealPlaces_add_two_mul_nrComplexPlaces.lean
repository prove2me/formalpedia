-- Prove2me | solution 1 for DirichletUnitTheorem.degree_eq_nrRealPlaces_add_two_mul_nrComplexPlaces
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:19:27.532989+00:00
-- url     : https://prove2.me/submissions/0a84ceac-2e70-4a72-a575-b99c1e0239a1

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K]
    [NumberField K] :
    InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
  InfinitePlace.card_add_two_mul_card_eq_rank K
