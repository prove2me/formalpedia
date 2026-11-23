-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.span_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:15.552125+00:00
-- url     : https://prove2.me/submissions/48b59da4-54d2-41c7-8ccc-459c807017cc

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (A : FI E) (c : E) (hc : c ∈ A) :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ c ≤ A := by
  intro y hy
  rw [FractionalIdeal.mem_spanSingleton] at hy
  obtain ⟨z, rfl⟩ := hy
  exact A.coeToSubmodule.smul_mem z hc
end Formalism.FourierDecayAlt.P.S6x2
