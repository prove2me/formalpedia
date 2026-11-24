-- Prove2me | solution 1 for FunctorialResolution.Blowup.algebraMap_chart_eq_chartRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:20.449801+00:00
-- url     : https://prove2.me/submissions/f30574de-fc09-4e3b-b149-950f9bb4a539

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
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) =
      chartRingHom I a := rfl
end FunctorialResolution.Blowup
