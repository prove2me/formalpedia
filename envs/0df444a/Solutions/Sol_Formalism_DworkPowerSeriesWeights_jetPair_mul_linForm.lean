-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_mul_linForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:41.691804+00:00
-- url     : https://prove2.me/submissions/e148c4bd-e70c-43a0-ab1b-2e27fb53338c

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_apply
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_X
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (P : MvPolynomial ι K) (L : ι → K) (F : MvPowerSeries ι K) :
    jetPair (P * linForm L) F = jetPair P (dirD L F) := by
  unfold linForm
  rw [Finset.mul_sum, jetPair_sum_left, dirD_apply, jetPair_sum_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [jetPair_C_mul_right, ← jetPair_mul_X, ← jetPair_C_mul_left]
  congr 1
  ring
end Formalism.DworkPowerSeriesWeights
