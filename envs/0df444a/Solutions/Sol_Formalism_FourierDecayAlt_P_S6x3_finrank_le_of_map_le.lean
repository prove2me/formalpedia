-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.finrank_le_of_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.197404+00:00
-- url     : https://prove2.me/submissions/cca5f78d-c7cd-426f-8392-97e8c7ed5ede

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (f : E →ₗ[ℤ] E) (hf : Function.Injective f) (N N' : Submodule ℤ E)
    [Module.Finite ℤ N'] (h : N.map f ≤ N') : finrank ℤ N ≤ finrank ℤ N' := by
  rw [(Submodule.equivMapOfInjective f hf N).finrank_eq]
  exact Submodule.finrank_mono h
end Formalism.FourierDecayAlt.P.S6x3
