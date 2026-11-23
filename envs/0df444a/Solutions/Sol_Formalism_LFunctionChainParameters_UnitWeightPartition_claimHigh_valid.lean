-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.UnitWeightPartition.claimHigh_valid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:14.99251+00:00
-- url     : https://prove2.me/submissions/3ea879e2-097c-49cf-a5ce-1038512ea090

import Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_weightedSlopeExcess_decomposition

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
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) :
    ClaimHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN := by
  unfold ClaimHigh
  intro H
  unfold HypHigh at H
  obtain ⟨hl, hsg', h1, h2⟩ := H
  have hsg := weightedSlopeExcess_decomposition W J l gain F E tau
  unfold ClaimSg at hsg
  have hle : Sg W l sg' tau ≤ Sg W l (sgw J gain F E) tau := by
    unfold Sg
    refine Finset.sum_le_sum (fun w hw => ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [hsg' w hw]) (by linarith [hl w hw])
  linarith
end Formalism.LFunctionChainParameters.UnitWeightPartition
