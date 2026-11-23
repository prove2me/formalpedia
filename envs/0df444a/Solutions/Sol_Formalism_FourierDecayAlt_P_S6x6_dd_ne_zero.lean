-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.dd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:08.164537+00:00
-- url     : https://prove2.me/submissions/eed908a0-d9b3-4f9a-9c9f-9547cefb3031

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution : dd E ≠ 0 := by
  unfold dd
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact differentIdeal_ne_bot
end Formalism.FourierDecayAlt.P.S6x6
