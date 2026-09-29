-- Prove2me | solution 1 for FamousTheorems.lasker_noether
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:15:45.146703+00:00
-- url     : https://prove2.me/submissions/495aeeed-81c2-42fe-85a7-584d6025ffa7

import Mathlib

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M] (N : Submodule R M) :
    ∃ t : Finset (Submodule R M), N.IsMinimalPrimaryDecomposition t :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker R M) N
