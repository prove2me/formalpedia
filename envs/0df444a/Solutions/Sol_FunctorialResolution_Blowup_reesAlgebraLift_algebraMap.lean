-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesAlgebraLift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:52.358251+00:00
-- url     : https://prove2.me/submissions/8cdba090-05af-47bb-8cae-34f9131a2e19

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
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
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) (r : R) :
    reesAlgebraLift I φ s hI hs (algebraMap R ↥(reesAlgebra I) r) = φ r := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I φ s hI hs]
  have hcoe : ((algebraMap R ↥(reesAlgebra I) r : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.C r := rfl
  rw [hcoe]
  simp [polynomialEvalInvSelf]
end FunctorialResolution.Blowup
