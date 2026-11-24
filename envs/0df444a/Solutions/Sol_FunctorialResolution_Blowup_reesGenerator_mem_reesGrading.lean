-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesGenerator_mem_reesGrading
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:49:40.105586+00:00
-- url     : https://prove2.me/submissions/55134c78-53e3-470f-8ddb-27d4c28f0bef

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


theorem solution (I : Ideal R) (a : ↥I) : reesGenerator I a ∈ reesGrading I 1 := by
  apply (mem_reesGrading_iff_monomial I 1 _).2
  exact ⟨a.val, by simpa using a.property, rfl⟩
