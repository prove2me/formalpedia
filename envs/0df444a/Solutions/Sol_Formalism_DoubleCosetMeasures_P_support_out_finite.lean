-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.support_out_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:24.219053+00:00
-- url     : https://prove2.me/submissions/30ff8742-2496-4805-b986-4b54743c5009

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {X : Type}
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (f : X → E)
    (hc : HasCompactSupport f) :
    (Function.support (fun q : Quotient r => f q.out)).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (cls r) hr (by
    intro x _; exact Set.mem_iUnion.2 ⟨Quotient.mk r x, rfl⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', hm⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have hqq : q = q' := (Quotient.out_eq q).symm.trans hm
  exact hqq ▸ hq'
end Formalism.DoubleCosetMeasures.P
