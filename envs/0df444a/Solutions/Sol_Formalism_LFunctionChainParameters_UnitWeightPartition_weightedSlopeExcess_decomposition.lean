-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.UnitWeightPartition.weightedSlopeExcess_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:04.527123+00:00
-- url     : https://prove2.me/submissions/d4137ad4-3062-460f-b154-0c46a5585b5e

import Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.UnitWeightPartition
open Finset
variable {ι κ : Type*} [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.UnitWeightPartition
theorem _root_.solution (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : ClaimSg W J l gain F E tau := by
  have hF : ∑ j ∈ J, ∑ w ∈ W, l w * F j w = ∑ w ∈ W, ∑ j ∈ J, l w * F j w := Finset.sum_comm
  have hE : ∑ j ∈ J, ∑ w ∈ W, l w * E j w = ∑ w ∈ W, ∑ j ∈ J, l w * E j w := Finset.sum_comm
  unfold ClaimSg Sg sgw Ga Fo Ee
  rw [hF, hE, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
end Formalism.LFunctionChainParameters.UnitWeightPartition
