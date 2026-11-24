-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.UnitWeightPartition.unit_weight_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:41.230189+00:00
-- url     : https://prove2.me/submissions/54e319ba-77a0-4d2b-b086-5d8ae8c1e55f

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
theorem _root_.solution (W : Finset ι) (P : Finset ℕ) (pr : ι → ℕ) (l io : ι → ℝ)
    (iop : ℕ → ℝ) : ClaimUnit W P pr l io iop := by
  unfold ClaimUnit
  intro hP hl hio
  have hmain : 2 * ∑ w ∈ W, l w * io w = 2 * ∑ p ∈ P, Real.log (p : ℝ) * iop p := by
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to hP]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← hl p hp, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [Finset.mem_filter] at hw
    rw [hio w hw.1, hw.2]
  refine Eq.trans ?_ hmain
  first | rfl | (show ∑ w ∈ W, 2 * l w * io w = _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => mul_assoc _ _ _)) | (show ∑ w ∈ W, 2 * (l w * io w) = _; rw [Finset.mul_sum])
end Formalism.LFunctionChainParameters.UnitWeightPartition
