-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:13.449694+00:00
-- url     : https://prove2.me/submissions/ffc42cc9-e5ab-4d6e-a98d-4020db9dc9bc

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
theorem _root_.solution (x : 𝓞 E) :
    ringOfIntegersComplexConj E (ringOfIntegersComplexConj E x) = x := by
  apply RingOfIntegers.ext
  simp [complexConj_apply_apply]
end Formalism.FourierDecayAlt.P.S6x6
