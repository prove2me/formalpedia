-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:10.921915+00:00
-- url     : https://prove2.me/submissions/9e5781ca-04b9-4234-86ee-7bf7b94cefb9

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_mul

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
theorem _root_.solution (A : FI E) (hA : ConjStable E A) (n : ℕ) : ConjStable E (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact conjStable_one E
  | succ n ih => rw [pow_succ]; exact conjStable_mul E _ _ ih hA
end Formalism.FourierDecayAlt.P.S6x2
