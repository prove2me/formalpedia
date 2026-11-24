-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:57.872801+00:00
-- url     : https://prove2.me/submissions/3528be36-4fcd-4f29-b50d-e676d26863e0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_basicOpen

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
theorem _root_.solution (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]
end FunctorialResolution.EmbeddedResolution
