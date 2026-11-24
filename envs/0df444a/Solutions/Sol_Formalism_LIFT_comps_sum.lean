-- Prove2me | solution 1 for Formalism.LIFT.comps_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:31:41.493667+00:00
-- url     : https://prove2.me/submissions/1f2d21ce-17fb-4893-ad35-764baf627053

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comps_zero
import Theorems.Thm_Formalism_LIFT_comps_add

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Comps φA ε aa ℓ (f i)) :
    Comps φA ε aa ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ => comps_add φA ε aa) (comps_zero φA ε aa) h
end Formalism.LIFT
