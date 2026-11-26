-- Prove2me | solution 1 for FourierJacobi.Analysis.coreAtCentral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:45.6355+00:00
-- url     : https://prove2.me/submissions/8310229c-9249-487e-bebc-901cb28c4937

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution (z : K) : Measurable (coreAtCentral K z) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.prodMk measurable_const))
end FourierJacobi.Analysis
