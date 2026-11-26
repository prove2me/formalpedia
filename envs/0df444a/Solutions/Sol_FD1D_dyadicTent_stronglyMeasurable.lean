-- Prove2me | solution 1 for FD1D.dyadicTent_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:51.709679+00:00
-- url     : https://prove2.me/submissions/dd4efe1c-39db-4ed6-aa5f-b401879e00d1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution (l p : ℝ) :
    StronglyMeasurable (dyadicTent l p) := by
  exact (((continuous_id.sub continuous_const).div_const p).stronglyMeasurable.indicator
      measurableSet_Icc).add
    (((continuous_const.sub continuous_id).div_const p).stronglyMeasurable.indicator
      measurableSet_Ioc)
end FD1D
