-- Prove2me | solution 1 for Eden.tendsto_log_radialAmplitude_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:16.010693+00:00
-- url     : https://prove2.me/submissions/481f438d-6bd1-4eb4-839c-b6fbdb6c7f8d

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_tendsto_squaredRadiusEvolution_all
import Theorems.Thm_Eden_hasDerivAt_log_radialAmplitude
import Theorems.Thm_Eden_tendsto_div_time_of_hasDerivAt


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => Real.log (radialAmplitude t s) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) := by
  apply tendsto_div_time_of_hasDerivAt
    (fun t ht => hasDerivAt_log_radialAmplitude ht hs)
  have hcont : Continuous radialRate := by unfold radialRate; fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_squaredRadiusEvolution_all s)
end Eden
