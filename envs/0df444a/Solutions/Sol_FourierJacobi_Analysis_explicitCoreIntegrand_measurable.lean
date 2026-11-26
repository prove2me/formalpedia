-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitCoreIntegrand_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:11.12183+00:00
-- url     : https://prove2.me/submissions/b555f641-3d65-497a-b37e-031caa11a108

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_measurable
import Theorems.Thm_FourierJacobi_Analysis_coreAtCentral_measurable
import Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelHeight_measurable


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
theorem _root_.solution (q : ℝ) (a b d : ℂ) (T : ℝ) (z : K) :
    Measurable (explicitCoreIntegrand K q a b d T z) := by
  have hk : Measurable (fun p : HaarPoint K => coreScaleExponent K p.1) :=
    (coreScaleExponent_measurable K).comp measurable_fst
  have hscale : Measurable (fun n : ℤ =>
      d ^ n * (Real.rpow (q ^ (-n)) (3 / 2) : ℂ)) := measurable_of_countable _
  have hheight := ((measurable_of_countable (fun n : ℤ => (T : ℂ) ^ n)).comp
    (kernelHeight_measurable K)).comp (coreAtCentral_measurable K z)
  exact ((hscale.comp hk).mul hheight).mul
    ((explicitWeylKernel_measurable K (inverseSqrt q : ℂ) a b).comp
      (coreAtCentral_measurable K z))
end FourierJacobi.Analysis
