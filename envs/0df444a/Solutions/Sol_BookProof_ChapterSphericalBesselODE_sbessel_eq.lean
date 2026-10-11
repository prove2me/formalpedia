-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.sbessel_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:35.3083+00:00
-- url     : https://prove2.me/submissions/83929fc3-e36e-4b1a-b5f0-8f2a34285867

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.sbessel_eq
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) (r : ℝ) : sbessel l r = r ^ l * gIter l r := rfl
