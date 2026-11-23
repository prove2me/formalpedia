-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.locAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:38.17962+00:00
-- url     : https://prove2.me/submissions/190911d4-9a4f-48e5-b8f8-e31165765cf3

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
variable {E}
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution (L : Submodule ℤ E) {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) :
    (0 : E) ∈ locAt E P L :=
  ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h), by simp⟩
end Formalism.FourierDecayAlt.P.S6x6
