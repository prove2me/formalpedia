-- Prove2me | solution 1 for Formalism.LIFT.comps_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:56.565927+00:00
-- url     : https://prove2.me/submissions/55a34f51-93ac-48f3-bc92-0e38a53ffab3

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comps_mul_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
namespace Formalism.LIFT
theorem _root_.solution (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) (n : ℕ) {x : A}
    (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (ε ^ n * x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact comps_mul_eps φA ε aa hℓ hε ih
end Formalism.LIFT
