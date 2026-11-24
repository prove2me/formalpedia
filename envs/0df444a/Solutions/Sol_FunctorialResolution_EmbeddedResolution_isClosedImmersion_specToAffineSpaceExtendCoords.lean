-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isClosedImmersion_specToAffineSpaceExtendCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:30.645131+00:00
-- url     : https://prove2.me/submissions/08fddb53-ce81-41d7-adf8-36287b9a2f3b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ σ.hom b p = x) :
    AlgebraicGeometry.IsClosedImmersion (specToAffineSpaceExtendCoords k A pA M e σ n b) :=
  AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _
    (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)
end FunctorialResolution.EmbeddedResolution
