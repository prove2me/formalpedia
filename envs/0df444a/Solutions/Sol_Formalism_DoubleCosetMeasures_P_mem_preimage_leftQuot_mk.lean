-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.mem_preimage_leftQuot_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:21.674318+00:00
-- url     : https://prove2.me/submissions/dee90bde-e632-4145-b5a2-d2de919b0157

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided

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
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G) (q : G ⧸ K) (y : G) :
    (y : G ⧸ K) = q ↔ q.out⁻¹ * y ∈ K := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev, inv_inv]
end Formalism.DoubleCosetMeasures.P
