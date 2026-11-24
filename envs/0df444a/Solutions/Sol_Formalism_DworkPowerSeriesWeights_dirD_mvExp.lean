-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:23.912509+00:00
-- url     : https://prove2.me/submissions/4413d6c8-f557-4f25-86d4-54ff20fd7d39

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_apply
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (L : ι → K) (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    dirD L (mvExp f) = dirD L f * mvExp f := by
  rw [dirD_apply, dirD_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold mvExp
  rw [Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]
  ring
end Formalism.DworkPowerSeriesWeights
