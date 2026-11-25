-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.liftDerivationOfKerEqSpan_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:31.868879+00:00
-- url     : https://prove2.me/submissions/a5cf1386-b852-4c83-80cc-9d8fa8d36ec3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (π : R →ₐ[k] S) (hπ : Function.Surjective π)
    (h : R) (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) (r : R) :
    liftDerivationOfKerEqSpan π hπ h hker D hD (π r) = π (D r) :=
  D.liftOfSurjective_apply hπ (algHom_map_derivation_eq_zero π h hker D hD) r
end FunctorialResolution.EmbeddedResolution
