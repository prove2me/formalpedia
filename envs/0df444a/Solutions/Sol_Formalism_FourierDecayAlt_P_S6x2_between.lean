-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.between
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:12.941875+00:00
-- url     : https://prove2.me/submissions/b954784e-e25d-4406-b0cb-49f3d4035352

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_mem_twLat

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
theorem _root_.solution : Between := by
  intro E _ _ _ A B s hBA hB
  refine ⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩
  rw [mem_twLat]
  refine ⟨hBA ht, ?_⟩
  have h1 : complexConj E t ∈ B := hB t ht
  have h2 : (-1 : E) ^ s * complexConj E t ∈ B := by
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · simpa using h1
    · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
  exact B.coeToSubmodule.sub_mem ht h2
end Formalism.FourierDecayAlt.P.S6x2
