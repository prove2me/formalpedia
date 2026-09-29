-- Prove2me | solution 1 for FamousTheorems.right_adjoints_preserve_limits_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:04:33.983355+00:00
-- url     : https://prove2.me/submissions/295a3b6f-2b94-4a3f-bb04-4e0c532ea1e3

import Mathlib

universe u v w w'

theorem solution {C D : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D] {F : CategoryTheory.Functor C D}
    {G : CategoryTheory.Functor D C} (adj : CategoryTheory.Adjunction F G) :
    CategoryTheory.Limits.PreservesLimitsOfSize.{w, w'} G :=
  adj.rightAdjoint_preservesLimits
