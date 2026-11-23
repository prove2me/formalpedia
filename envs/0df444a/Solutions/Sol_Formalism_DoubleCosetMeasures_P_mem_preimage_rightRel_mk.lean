-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.mem_preimage_rightRel_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:30.639671+00:00
-- url     : https://prove2.me/submissions/80c0ca56-26cc-4356-bb2a-61ff7279f00c

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
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel K)) (x : G) :
    Quotient.mk (QuotientGroup.rightRel K) x = q ↔ x * q.out⁻¹ ∈ K := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← K.inv_mem_iff, mul_inv_rev, inv_inv]
end Formalism.DoubleCosetMeasures.P
