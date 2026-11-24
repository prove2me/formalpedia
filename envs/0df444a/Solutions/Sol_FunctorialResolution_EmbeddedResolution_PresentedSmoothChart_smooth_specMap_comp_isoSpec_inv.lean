-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:35.798663+00:00
-- url     : https://prove2.me/submissions/85613479-7eef-49e8-997f-97a35921ca6e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffineLiftRelativeDimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffinePullbackPresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PresentedSmoothChart
namespace FunctorialResolution.EmbeddedResolution.PresentedSmoothChart
theorem _root_.solution {A : Scheme.{u}} [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B')
    (hσ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom σ)) :
    AlgebraicGeometry.Smooth (Spec.map σ ≫ A.isoSpec.inv) := by
  have hs : RingHom.Smooth (CommRingCat.Hom.hom σ) := by
    let := (CommRingCat.Hom.hom σ).toAlgebra
    have : Algebra.IsStandardSmooth ↥Γ(A, ⊤) ↥B' := hσ
    exact ⟨inferInstance, inferInstance⟩
  have h1 : AlgebraicGeometry.Smooth (Spec.map σ) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr hs
  have h2 : AlgebraicGeometry.Smooth A.isoSpec.inv := inferInstance
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) _ _ h1 h2
end FunctorialResolution.EmbeddedResolution.PresentedSmoothChart
