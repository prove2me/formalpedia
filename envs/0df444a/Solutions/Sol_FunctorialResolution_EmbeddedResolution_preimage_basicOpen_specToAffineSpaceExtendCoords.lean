-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.preimage_basicOpen_specToAffineSpaceExtendCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:14.266263+00:00
-- url     : https://prove2.me/submissions/36fac756-90ac-4e95-9f13-77106f5b6319

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections

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
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤))
    (hf : IsUnit ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f)) :
    (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).basicOpen f) = ⊤ := by
  have h1 : (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).basicOpen f) =
      (Spec B').basicOpen ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f) :=
    Scheme.preimage_basicOpen ..
  have h2 : (Spec B').basicOpen ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f) = ⊤ :=
    Scheme.basicOpen_of_isUnit (Spec B') hf
  rw [h1, h2]
end FunctorialResolution.EmbeddedResolution
