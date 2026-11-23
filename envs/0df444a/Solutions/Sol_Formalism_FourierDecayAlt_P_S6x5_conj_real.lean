-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.conj_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:20.2217+00:00
-- url     : https://prove2.me/submissions/3de9ca63-0618-4b10-83c8-44f57b113341

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)
end Formalism.FourierDecayAlt.P.S6x5
