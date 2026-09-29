-- Prove2me | solution 1 for FamousTheorems.bipolar_proper_cone_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:44:11.082552+00:00
-- url     : https://prove2.me/submissions/7ad60e5f-8c84-4717-b0c0-cc289a6fd984

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (C : ProperCone ℝ E) :
    ProperCone.innerDual (ProperCone.innerDual (C : Set E) : Set E) = C :=
  ProperCone.innerDual_innerDual C
