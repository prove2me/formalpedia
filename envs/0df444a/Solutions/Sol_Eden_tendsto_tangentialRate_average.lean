-- Prove2me | solution 1 for Eden.tendsto_tangentialRate_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:39.334363+00:00
-- url     : https://prove2.me/submissions/64a3739d-720b-4685-8f77-074cf336ec47

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_tendsto_log_planarAmplitude_div
import Theorems.Thm_Eden_log_planarAmplitude_eq_integral


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      tangentialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) := by
  apply (tendsto_log_planarAmplitude_div hs).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [log_planarAmplitude_eq_integral ht hs]
end Eden
