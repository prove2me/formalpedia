-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.dual_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:10.676582+00:00
-- url     : https://prove2.me/submissions/54b3113d-a535-459e-ad8d-851ee84c40a0

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_one

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
theorem _root_.solution (ν : ℤ) :
    FractionalIdeal.dual ℤ ℚ (dd E ^ ν) = dd E ^ (-(ν + 1)) := by
  rw [FractionalIdeal.dual_eq_mul_inv, dual_one, neg_add, zpow_add₀ (dd_ne_zero E), zpow_neg,
    zpow_neg, zpow_one, mul_comm]
end Formalism.FourierDecayAlt.P.S6x2
