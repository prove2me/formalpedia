-- Prove2me | solution 1 for Eden.globalGrowthRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:14.748732+00:00
-- url     : https://prove2.me/submissions/2f91f4b1-471e-48ec-930c-462232a29075

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_globalLogGrowth_nonneg
import Theorems.Thm_Eden_tendsto_globalGrowthRate


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 4) {c : ℝ} (hc : 4 ≤ c) :
    0 ≤ globalGrowthRate c k := by
  apply ge_of_tendsto (tendsto_globalGrowthRate (by omega) hc)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact div_nonneg (globalLogGrowth_nonneg hk hc ht) ht
end Eden
