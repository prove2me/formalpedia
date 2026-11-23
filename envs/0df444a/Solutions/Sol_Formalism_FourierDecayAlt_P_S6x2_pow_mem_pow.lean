-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.pow_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:13.073903+00:00
-- url     : https://prove2.me/submissions/f724c638-45a3-4f3c-87f0-a7f789a94669

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
theorem _root_.solution (A : FI E) (x : E) (hx : x ∈ A) (n : ℕ) : x ^ n ∈ A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact FractionalIdeal.one_mem_one _
  | succ n ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx
end Formalism.FourierDecayAlt.P.S6x2
