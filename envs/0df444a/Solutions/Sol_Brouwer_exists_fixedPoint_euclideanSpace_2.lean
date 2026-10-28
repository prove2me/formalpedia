-- Prove2me | solution 2 for Brouwer.exists_fixedPoint_euclideanSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:54:06.040468+00:00
-- url     : https://prove2.me/submissions/baf0277b-18ac-4b55-94df-cec9732fa66b

import Mathlib
import Theorems.Thm_AGT_brouwer_fixed_point

open Metric Set MeasureTheory

-- The Euclidean case is the general statement at `E = EuclideanSpace ℝ (Fin d)`, which is a
-- finite-dimensional real normed space, so nothing is left to prove here.
theorem solution {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x :=
  AGT.brouwer_fixed_point hKconv hKcpt hKne f hf hfK
