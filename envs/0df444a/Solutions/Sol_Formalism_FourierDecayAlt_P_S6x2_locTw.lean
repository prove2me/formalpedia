-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.locTw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:24.504877+00:00
-- url     : https://prove2.me/submissions/fcd3b91a-3ed3-4036-89b3-c5f6fe22f144

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_smul_mem_FI

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
theorem _root_.solution : LocTw := by
  intro E _ _ _ A B s P hP t
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_twLat] at h
    refine ⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩
    have := h.2
    rw [map_mul, conj_real] at this
    show _ ∈ B
    convert this using 1; ring
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
    rw [mem_twLat]
    constructor
    · have := smul_mem_FI E A b _ h1
      rw [map_mul]; convert this using 1; ring
    · have := smul_mem_FI E B a _ h2
      rw [map_mul, map_mul, map_mul, conj_real, conj_real]; convert this using 1; ring
end Formalism.FourierDecayAlt.P.S6x2
