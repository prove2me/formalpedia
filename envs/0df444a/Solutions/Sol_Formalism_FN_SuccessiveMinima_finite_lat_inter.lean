-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.finite_lat_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:49.759472+00:00
-- url     : https://prove2.me/submissions/11dc1c40-4a89-4446-ad0a-834e753624ad

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.FN Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.FN.SuccessiveMinima
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}
    (hs : Bornology.IsBounded s) : ((L : Set E) ∩ s).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hcl : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discrete
  have hd : IsDiscrete (L : Set E) := by
    first
      | exact ⟨‹DiscreteTopology L›⟩
      | exact isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›
  rw [Set.inter_comm]
  exact Metric.finite_isBounded_inter_isClosed hd hs hcl
end Formalism.FN.SuccessiveMinima
