-- Prove2me | solution 1 for Eden.continuousOn_squaredRadiusEvolution_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:00.240675+00:00
-- url     : https://prove2.me/submissions/f95576b8-f091-47e2-aa68-237875eb430f

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) :
    ContinuousOn (fun t => squaredRadiusEvolution t s) (Ici 0) :=
  fun _ ht => (hasDerivAt_squaredRadiusEvolution ht s).continuousAt.continuousWithinAt
end Eden
