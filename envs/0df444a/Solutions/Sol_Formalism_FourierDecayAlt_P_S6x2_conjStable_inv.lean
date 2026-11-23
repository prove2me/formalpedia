-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:12.911901+00:00
-- url     : https://prove2.me/submissions/9f1b1e3e-effa-488d-be5a-cebf60c0f791

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_one

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
theorem _root_.solution (A : FI E) (hA0 : A ≠ 0) (hA : ConjStable E A) : ConjStable E A⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff hA0] at hx ⊢
  intro y hy
  have := conjStable_one E _ (hx _ (hA y hy))
  rwa [map_mul, complexConj_apply_apply] at this
end Formalism.FourierDecayAlt.P.S6x2
