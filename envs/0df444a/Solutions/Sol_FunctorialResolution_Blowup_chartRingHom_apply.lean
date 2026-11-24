-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:22.454863+00:00
-- url     : https://prove2.me/submissions/fbfc3aba-fa5e-4129-b15c-71bf24f3de2d

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
theorem _root_.solution (I : Ideal R) (a : ↥I) (r : R) :
    chartRingHom I a r =
      HomogeneousLocalization.fromZeroRingHom (reesGrading I) (Submonoid.powers (reesGenerator I a))
        (reesDegreeZeroEquiv I r) := rfl
end FunctorialResolution.Blowup
