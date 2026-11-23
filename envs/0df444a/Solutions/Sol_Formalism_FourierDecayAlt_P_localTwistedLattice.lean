-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.localTwistedLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:24.270115+00:00
-- url     : https://prove2.me/submissions/4bf4c161-ca6f-42f8-bd30-a343bde8a418

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x1_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x1_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x1_smul_mem_FI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.LocTw := by
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
end Formalism.FourierDecayAlt.P
