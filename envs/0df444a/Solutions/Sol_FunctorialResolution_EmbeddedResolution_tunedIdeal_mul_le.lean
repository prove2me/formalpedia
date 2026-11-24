-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:57.094177+00:00
-- url     : https://prove2.me/submissions/ab5b6a87-baa4-4068-938b-615ce2f8849f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_fun_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_mul_fun_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_eq_iSup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal

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
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m s t : ℕ) :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by
  rw [tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, Submodule.iSup_mul]
  refine iSup_le fun c => ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun hc => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun d => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun hd => ?_
  rw [tuningMonomial_mul_fun_add]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_fun_add]
  exact Nat.add_le_add hc hd
end FunctorialResolution.EmbeddedResolution
