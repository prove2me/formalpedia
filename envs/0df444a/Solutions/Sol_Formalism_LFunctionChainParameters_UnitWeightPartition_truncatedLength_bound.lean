-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.UnitWeightPartition.truncatedLength_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:39.603432+00:00
-- url     : https://prove2.me/submissions/7b4f731b-40c4-4a03-a661-c055eb0ddd67

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
theorem _root_.solution (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) :
    ClaimT WT l len dM du de lam T := by
  unfold ClaimT
  intro hl hdM hde0 hde1 hdu hlam hlen hsum
  have hdu0 : 0 < du := by rw [hdu]; exact mul_pos (by linarith) hdM
  have hdu2 : dM ≤ 2 * du := by
    rw [hdu]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * de) hdM.le]
  calc ∑ w ∈ WT, 2 * l w * len w / du ≤ ∑ w ∈ WT, 4 * lam * l w := by
        refine Finset.sum_le_sum (fun w hw => ?_)
        rw [div_le_iff₀ hdu0]
        have h1 := hl w hw
        have h2 := hlen w hw
        nlinarith [mul_nonneg h1 (sub_nonneg.2 h2),
          mul_nonneg (mul_nonneg h1 hlam) (sub_nonneg.2 hdu2)]
    _ = 4 * lam * Real.log T := by rw [← Finset.mul_sum, hsum]
end Formalism.LFunctionChainParameters.UnitWeightPartition
