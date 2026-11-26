-- Prove2me | solution 1 for Eden.limiting_rates_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:04.831194+00:00
-- url     : https://prove2.me/submissions/494f2583-d790-4845-93c6-8e3dde344e33

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    radialRate (limitingSquaredRadius s) = -4 ∧
      tangentialRate (limitingSquaredRadius s) = 0 := by
  norm_num [limitingSquaredRadius, not_lt.mpr hs.le, ne_of_gt hs, radialRate, tangentialRate]
end Eden
