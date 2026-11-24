-- Prove2me | solution 1 for Formalism.LIFT.comps_of_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:28.743864+00:00
-- url     : https://prove2.me/submissions/d18a6241-0340-43d7-a1b3-a31b99898e41

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comps_zero
import Theorems.Thm_Formalism_LIFT_comps_add
import Theorems.Thm_Formalism_LIFT_comps_mul
import Theorems.Thm_Formalism_LIFT_comps_phi

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
    {x : A} (hx : x ∈ Ideal.map φA aa) : Comps φA ε aa ℓ x := by
  let S : Ideal A :=
    { carrier := {x | Comps φA ε aa ℓ x}
      add_mem' := fun ha hb => comps_add φA ε aa ha hb
      zero_mem' := comps_zero φA ε aa
      smul_mem' := fun r _ hx => comps_mul φA ε aa hℓ hε hU r hx }
  have hle : Ideal.map φA aa ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun a ha => comps_phi φA ε aa hℓ ha
  exact hle hx
end Formalism.LIFT
