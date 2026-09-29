-- Prove2me | solution 1 for FamousTheorems.general_adjoint_functor_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:35.040899+00:00
-- url     : https://prove2.me/submissions/7192ecf4-c3bc-470e-be77-bc63cf98ba0b

import Mathlib

universe u v u₁ v₁

theorem solution {C : Type u} [CategoryTheory.Category.{v} C] {D : Type u₁} [CategoryTheory.Category.{v₁} D]
    (G : CategoryTheory.Functor D C) [CategoryTheory.Limits.HasLimits D]
    [CategoryTheory.Limits.PreservesLimitsOfSize.{v₁, v₁} G] (hG : CategoryTheory.SolutionSetCondition.{v₁} G) :
    G.IsRightAdjoint :=
  CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG
