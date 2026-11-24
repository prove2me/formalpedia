-- Prove2me | solution 1 for Formalism.LIFT.comps_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:01.50008+00:00
-- url     : https://prove2.me/submissions/27641825-5e1c-4ecd-aaa7-b3e8b2355c50

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comps_mul_phi
import Theorems.Thm_Formalism_LIFT_comps_mul_pow
import Theorems.Thm_Formalism_LIFT_comps_sum

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
theorem _root_.solution (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (r : A) {x : A} (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (r * x) := by
  obtain ⟨e, he⟩ := (hU r).exists
  rw [he, sum_mul]
  refine comps_sum φA ε aa _ _ fun i _ => ?_
  rw [mul_assoc]
  exact comps_mul_pow φA ε aa hℓ hε _ (comps_mul_phi φA ε aa _ hx)
end Formalism.LIFT
