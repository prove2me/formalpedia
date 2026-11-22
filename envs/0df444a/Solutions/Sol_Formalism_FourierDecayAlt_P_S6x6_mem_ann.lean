-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.mem_ann
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:12:49.102584+00:00
-- url     : https://prove2.me/submissions/8e8d6044-6c02-4f88-bfaa-a56e3a4d649b

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
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (a : 𝓞 (maximalRealSubfield E)) :
    a ∈ ann hL t ↔ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L := Iff.rfl
end Formalism.FourierDecayAlt.P.S6x6
