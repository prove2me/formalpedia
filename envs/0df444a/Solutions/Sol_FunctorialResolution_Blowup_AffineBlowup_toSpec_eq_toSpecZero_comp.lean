-- Prove2me | solution 1 for FunctorialResolution.Blowup.AffineBlowup.toSpec_eq_toSpecZero_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:19.99795+00:00
-- url     : https://prove2.me/submissions/dd4e0ae8-0edc-4264-8b06-a857c8a4f8cc

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
open FunctorialResolution.Blowup.AffineBlowup
namespace FunctorialResolution.Blowup.AffineBlowup
theorem _root_.solution (I : Ideal R) :
    toSpec I =
      AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))) := rfl
end FunctorialResolution.Blowup.AffineBlowup
