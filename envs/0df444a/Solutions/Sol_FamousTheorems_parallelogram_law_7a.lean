-- Prove2me | solution 1 for FamousTheorems.parallelogram_law_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:42:32.589284+00:00
-- url     : https://prove2.me/submissions/cb3c090e-1fca-41f9-9038-8b526568ca96

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  parallelogram_law_with_norm ℝ x y
