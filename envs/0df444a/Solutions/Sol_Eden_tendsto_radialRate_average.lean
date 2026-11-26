-- Prove2me | solution 1 for Eden.tendsto_radialRate_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:37.180206+00:00
-- url     : https://prove2.me/submissions/7604377d-2e5b-4498-b7d7-3c202a220997

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_tendsto_log_radialAmplitude_div
import Theorems.Thm_Eden_log_radialAmplitude_eq_integral


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      radialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) := by
  apply (tendsto_log_radialAmplitude_div hs).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [log_radialAmplitude_eq_integral ht hs]
end Eden
