-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_linSer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:32.569082+00:00
-- url     : https://prove2.me/submissions/7b7458e1-9455-4ffd-b29a-36c27e3cab70

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_X
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_C

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
theorem _root_.solution (c : ι → ι → K) (L L' : ι → K) :
    dirD L' (linSer c L) = MvPowerSeries.C (polar c L L') := by
  unfold linSer polar
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Derivation.leibniz, dirD_X, dirD_C, smul_eq_mul, map_add, map_mul]
  ring
end Formalism.DworkPowerSeriesWeights
