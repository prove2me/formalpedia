-- Prove2me | solution 2 for FunctorialResolution.Blowup.reesGenerator_mem_reesGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:08.492715+00:00
-- url     : https://prove2.me/submissions/68cb26e3-fc0b-4002-b180-55e59c3c66b2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeOneMonomial_mem_reesGrading

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
theorem _root_.solution (I : Ideal R) (a : ↥I) : reesGenerator I a ∈ reesGrading I 1 :=
  reesDegreeOneMonomial_mem_reesGrading I a.2
end FunctorialResolution.Blowup
