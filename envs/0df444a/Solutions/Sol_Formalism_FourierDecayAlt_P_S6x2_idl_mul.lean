-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.idl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:08.10251+00:00
-- url     : https://prove2.me/submissions/09fb7c87-a170-492d-8c1e-ccca57ce777e

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
theorem _root_.solution (g : ℕ) (k ν : ℤ) (hg : 0 < g) :
    idl E g k ν * FractionalIdeal.spanSingleton _ (g : E) = idl E g (k + 1) ν := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  unfold idl
  rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add_one₀ hgE]
end Formalism.FourierDecayAlt.P.S6x2
