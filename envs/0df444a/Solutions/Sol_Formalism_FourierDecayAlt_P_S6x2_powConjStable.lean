-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.powConjStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:48.807923+00:00
-- url     : https://prove2.me/submissions/a0944225-4223-4283-97ea-e68a09e75a3a

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_zpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_dd
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_span

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
theorem _root_.solution : PowConjStable := by
  intro E _ _ _ g k ν
  unfold idl
  exact conjStable_mul E _ _ (conjStable_zpow E _ (dd_ne_zero E) (conjStable_dd E) ν)
    (conjStable_span E _ (by rw [map_zpow₀, map_natCast]))
end Formalism.FourierDecayAlt.P.S6x2
