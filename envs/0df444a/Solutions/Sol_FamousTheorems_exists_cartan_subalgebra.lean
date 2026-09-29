-- Prove2me | solution 1 for FamousTheorems.exists_cartan_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:17:33.738013+00:00
-- url     : https://prove2.me/submissions/e3a2d923-9b96-45f0-8353-97feed0c1a48

import Mathlib

theorem solution (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] [Infinite K] :
    ∃ x : L, (LieSubalgebra.engel K x).IsCartanSubalgebra :=
  LieAlgebra.exists_isCartanSubalgebra_engel K L
