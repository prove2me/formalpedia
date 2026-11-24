-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesDegreeOneMonomial_mem_reesGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:30.299456+00:00
-- url     : https://prove2.me/submissions/42b4be99-78a7-4d4b-8937-b250ea3628a8

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
theorem _root_.solution (I : Ideal R) {a : R} (ha : a ∈ I) :
    reesDegreeOneMonomial I a ha ∈ reesGrading I 1 :=
  reesMonomial_mem_reesGrading I (mem_pow_one I ha)
end FunctorialResolution.Blowup
