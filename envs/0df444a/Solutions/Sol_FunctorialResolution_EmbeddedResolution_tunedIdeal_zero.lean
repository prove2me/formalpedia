-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_zero
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:49:38.548816+00:00
-- url     : https://prove2.me/submissions/1be82bc5-ff0d-4bb3-8e63-70092dd4f130

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]


theorem solution (J : Ideal S) (m : ℕ) : tunedIdeal k J m 0 = ⊤ := by
  apply top_unique
  unfold tunedIdeal
  apply le_iSup_of_le (fun _ => 0)
  apply le_iSup_of_le (Nat.zero_le _)
  simp [tuningMonomial, Ideal.one_eq_top]
