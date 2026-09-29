-- Prove2me | solution 2 for FamousTheorems.exists_hilbert_basis
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:38:38.03862+00:00
-- url     : https://prove2.me/submissions/1cdb1365-c5bc-4ae3-bdfd-908654168de0

import Mathlib

theorem solution (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  exists_hilbertBasis 𝕜 E
