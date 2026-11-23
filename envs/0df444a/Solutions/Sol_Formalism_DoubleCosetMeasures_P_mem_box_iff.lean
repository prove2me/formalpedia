-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.mem_box_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.165255+00:00
-- url     : https://prove2.me/submissions/d9ddcad9-fb56-414d-b94b-dcbe7f26dc4b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_preimage_rightRel_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_preimage_leftQuot_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) (z : G₁ × G₂) :
    z ∈ box K₁ K₂ p ↔ clsTS K₁ K₂ z = p := by
  simp only [box, clsTS, Prod.ext_iff, Set.mem_prod, Set.mem_preimage, SetLike.mem_coe,
    mem_preimage_rightRel_mk, mem_preimage_leftQuot_mk]
end Formalism.DoubleCosetMeasures.P
