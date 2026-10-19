-- Prove2me | solution 2 for DirichletUnitTheorem.degree_eq_nrRealPlaces_add_two_mul_nrComplexPlaces
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:14:55.763636+00:00
-- url     : https://prove2.me/submissions/dfb2133c-dc99-43da-b99c-9c46d3e96517

import Mathlib
set_option autoImplicit false
open NumberField

theorem solution (K : Type*) [Field K]
    [NumberField K] :
    InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
  InfinitePlace.card_add_two_mul_card_eq_rank K
