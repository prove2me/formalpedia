-- Prove2me | solution 1 for FamousTheorems.caratheodory_convexity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:57.035202+00:00
-- url     : https://prove2.me/submissions/1c289baf-fec9-4f7b-9b67-d4f5d3813e61

import Mathlib

theorem solution {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (s : Set E) :
    convexHull 𝕜 s =
      ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t :=
  convexHull_eq_union
