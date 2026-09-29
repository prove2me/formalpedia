-- Prove2me | solution 1 for FamousTheorems.gelfand_transform_bijective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:52:11.75618+00:00
-- url     : https://prove2.me/submissions/6f335b21-b770-42c2-a03f-55f6c33d57d5

import Mathlib

theorem solution (A : Type*) [CommCStarAlgebra A] :
    Function.Bijective (WeakDual.gelfandTransform ℂ A) :=
  gelfandTransform_bijective A
