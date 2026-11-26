-- Prove2me | solution 1 for FourierJacobi.Analysis.kernelCartanFiber_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:58.03296+00:00
-- url     : https://prove2.me/submissions/3b17b7d1-2d06-4bd7-a347-a52c19a96a3a

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_d9a05d5624_103
omit [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution (p : KernelPoint K) :
    p ∈ kernelCartanFiber K (kernelN K p) (kernelB K p) := ⟨rfl,rfl⟩
end FourierJacobi.Analysis
