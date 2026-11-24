-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:36.380951+00:00
-- url     : https://prove2.me/submissions/38c4f4b4-fc58-4f51-b693-fb999b42a954

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open FunctorialResolution FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (r : R) :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := rfl
end FunctorialResolution.Blowup
