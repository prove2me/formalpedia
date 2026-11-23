-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x4.trace_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:20.067824+00:00
-- url     : https://prove2.me/submissions/a4f0408f-4cd6-4f98-a2bc-eb69d857c3be

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x4
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x4
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    Algebra.trace ℚ E (complexConj E x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv ((complexConj E).restrictScalars ℚ) x
end Formalism.FourierDecayAlt.P.S6x4
