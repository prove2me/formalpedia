-- Prove2me | solution 1 for Eden.tendsto_log_planarAmplitude_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:55.778929+00:00
-- url     : https://prove2.me/submissions/01a6ac53-e5ff-4fde-a361-e2ca1a267a8f

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_tendsto_squaredRadiusEvolution_all
import Theorems.Thm_Eden_hasDerivAt_log_planarAmplitude
import Theorems.Thm_Eden_tendsto_div_time_of_hasDerivAt


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => Real.log (planarAmplitude t s) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) := by
  apply tendsto_div_time_of_hasDerivAt
    (fun t ht => hasDerivAt_log_planarAmplitude ht hs)
  have hcont : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_squaredRadiusEvolution_all s)
end Eden
