-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheaf_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:33.570704+00:00
-- url     : https://prove2.me/submissions/c9a7ae79-f58e-4555-9f62-ab88a278ab7b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mul_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap


attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I J : X.IdealSheafData) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I * J)).ideal U ≤
        (I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have key := @derivIdeal_mul_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) (J.ideal U)
    have h1 : (derivIdealSheaf k p (I * J)).ideal U =
        @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U * J.ideal U) := by
      rw [derivIdealSheaf_ideal, hmul]
    have h2 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) =
        (derivIdealSheaf k p I).ideal U := (derivIdealSheaf_ideal k p I U).symm
    have h3 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (J.ideal U) =
        (derivIdealSheaf k p J).ideal U := (derivIdealSheaf_ideal k p J U).symm
    rw [h1]
    refine key.trans (sup_le ?_ ?_)
    · rw [h3, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_left U
    · rw [h2, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_right U
  exact h
end FunctorialResolution.EmbeddedResolution
