-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:11.029663+00:00
-- url     : https://prove2.me/submissions/c0b257b3-67a2-4386-b748-c04c38a5b989

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_apply

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
theorem _root_.solution (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, Scheme.preimage_basicOpen]
  rfl
end FunctorialResolution.EmbeddedResolution
