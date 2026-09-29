-- Prove2me | solution 1 for FamousTheorems.radon_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:09:41.529153+00:00
-- url     : https://prove2.me/submissions/51855f90-83f9-4d8c-b133-2875019e481e

import Mathlib

theorem solution {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I : Set ι, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty :=
  Convex.radon_partition h
