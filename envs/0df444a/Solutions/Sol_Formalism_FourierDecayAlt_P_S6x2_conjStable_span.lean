-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:51.888475+00:00
-- url     : https://prove2.me/submissions/d26c2c0b-41c5-4bb3-a0b7-a27c04fe188d

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
theorem _root_.solution (x : E) (hx : complexConj E x = x) :
    ConjStable E (FractionalIdeal.spanSingleton _ x) := by
  intro y hy
  rw [FractionalIdeal.mem_spanSingleton] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨ringOfIntegersComplexConj E z, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hx]
  rfl
end Formalism.FourierDecayAlt.P.S6x2
