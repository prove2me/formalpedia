-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesDegreeZeroEquiv_coe_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:01.895811+00:00
-- url     : https://prove2.me/submissions/48e1a59f-62e0-4e3b-a208-205c2c30c253

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply

set_option autoImplicit false
open Polynomial
open FunctorialResolution FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (r : R) :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  simp only [reesDegreeZeroEquiv_apply, reesDegreeZeroRingHom_coe_coe]
end FunctorialResolution.Blowup
