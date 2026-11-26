-- Prove2me | solution 1 for FourierJacobi.Analysis.coreLocalAbs_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:03.503029+00:00
-- url     : https://prove2.me/submissions/2d2b49e1-08d4-4f1c-8e3e-cf058b246dd6

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 < q) (a : Kˣ) :
    0 < coreLocalAbs K q a := zpow_pos hq _
end FourierJacobi.Analysis
