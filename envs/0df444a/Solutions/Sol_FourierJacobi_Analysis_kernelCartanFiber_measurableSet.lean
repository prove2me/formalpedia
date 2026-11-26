-- Prove2me | solution 1 for FourierJacobi.Analysis.kernelCartanFiber_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:14.21095+00:00
-- url     : https://prove2.me/submissions/a8c3169b-9197-4d4d-9884-600437a5fdb3

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Valuations_kernelB_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelN_measurable


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_d9a05d5624_103
namespace FourierJacobi.Analysis
theorem _root_.solution (n B : ℤ) :
    MeasurableSet (kernelCartanFiber K n B) :=
  ((measurableSet_singleton n).preimage (kernelN_measurable K)).inter
    ((measurableSet_singleton B).preimage (kernelB_measurable K))
end FourierJacobi.Analysis
