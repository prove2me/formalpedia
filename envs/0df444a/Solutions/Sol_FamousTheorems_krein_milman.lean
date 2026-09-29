-- Prove2me | solution 1 for FamousTheorems.krein_milman
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:30.170769+00:00
-- url     : https://prove2.me/submissions/7c6db497-acb3-424e-9198-81dd5075ac83

import Mathlib

open Filter Set Topology

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s :=
  closure_convexHull_extremePoints hscomp hAconv
