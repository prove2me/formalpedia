-- Prove2me | solution 1 for FD1D.dyadicTent_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:40.791062+00:00
-- url     : https://prove2.me/submissions/4649e295-5386-4130-a04d-07214340c848

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution (l p : ℝ) :
    Integrable (dyadicTent l p) := by
  apply Integrable.add
  · exact ((continuous_id.sub continuous_const).div_const p).integrableOn_Icc
      |>.integrable_indicator measurableSet_Icc
  · exact ((continuous_const.sub continuous_id).div_const p).integrableOn_Ioc
      |>.integrable_indicator measurableSet_Ioc
end FD1D
