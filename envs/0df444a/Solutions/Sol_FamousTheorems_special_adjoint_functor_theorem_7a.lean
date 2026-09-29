-- Prove2me | solution 1 for FamousTheorems.special_adjoint_functor_theorem_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:03:32.758986+00:00
-- url     : https://prove2.me/submissions/c060360b-3c9f-4679-b70b-1f142e93f2b4

import Mathlib

universe u v w

theorem solution {C : Type u} [CategoryTheory.Category.{v} C] {D : Type w} [CategoryTheory.Category.{v} D]
    [CategoryTheory.Limits.HasLimits D] [CategoryTheory.WellPowered.{v} D] {P : CategoryTheory.ObjectProperty D}
    [CategoryTheory.ObjectProperty.Small.{v} P] (hP : P.IsCoseparating) (G : CategoryTheory.Functor D C)
    [CategoryTheory.Limits.PreservesLimits G] : G.IsRightAdjoint :=
  CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating hP G
