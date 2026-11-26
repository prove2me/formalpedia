-- Prove2me | solution 1 for FourierJacobi.Analysis.coreScaleExponent_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:24.62419+00:00
-- url     : https://prove2.me/submissions/a12a251b-b921-4fdd-a105-ff1d73fb9e83

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
theorem _root_.solution (a : Kˣ) :
    (coreScaleExponent K a : WithTop ℤ) = localFieldValuation K (a : K) :=
  WithTop.coe_untop _ _
end FourierJacobi.Analysis
