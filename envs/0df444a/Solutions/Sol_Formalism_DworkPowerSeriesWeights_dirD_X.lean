-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:34.624365+00:00
-- url     : https://prove2.me/submissions/b714e91b-e003-4699-9f1f-fad49e875ec6

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_apply

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
theorem _root_.solution (L : ι → K) (x : ι) : dirD L (MvPowerSeries.X x) = MvPowerSeries.C (L x) := by
  classical
  rw [dirD_apply, Finset.sum_eq_single x]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro y _ hy
    rw [MvPowerSeries.pderiv_X_of_ne hy.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h
end Formalism.DworkPowerSeriesWeights
