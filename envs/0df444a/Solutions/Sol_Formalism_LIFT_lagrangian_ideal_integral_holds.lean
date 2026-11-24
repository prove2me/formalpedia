-- Prove2me | solution 1 for Formalism.LIFT.lagrangian_ideal_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:49.703196+00:00
-- url     : https://prove2.me/submissions/bb893db5-7638-4149-bf32-f2f4439e08e9

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal
import Theorems.Thm_Formalism_LIFT_lagrangian_ideal_holds

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
open Polynomial
namespace Formalism.LIFT
theorem _root_.solution : LagrangeIdealInt := by
  intro ℓ _ R _ _ S₁ S₂ c hdisj hw
  exact lagrangian_ideal_holds R (ℓ : R) ℤ S₁ S₂ c (fun a b => padicValInt ℓ (a - b)) hdisj hw
end Formalism.LIFT
