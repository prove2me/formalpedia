-- Prove2me | solution 1 for Formalism.LIFT.comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:31.977297+00:00
-- url     : https://prove2.me/submissions/78b38fc3-27ba-4799-88d8-71dbc28cb3e8

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comps_of_mem_map

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
    {x : A} (hx : x ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (he : x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) (i : Fin ℓ) : e i ∈ aa := by
  obtain ⟨e', he', hx'⟩ := comps_of_mem_map φA ε aa hℓ hε hU hx
  have : e = e' := (hU x).unique he hx'
  rw [this]
  exact he' i
end Formalism.LIFT
