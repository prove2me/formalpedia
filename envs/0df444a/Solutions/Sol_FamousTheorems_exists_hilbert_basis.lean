-- Prove2me | solution 1 for FamousTheorems.exists_hilbert_basis
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:37:30.795003+00:00
-- url     : https://prove2.me/submissions/3276961d-4cfe-4eb8-8441-b6b1ff3417ec

import Mathlib

theorem solution (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  exists_hilbertBasis 𝕜 E
