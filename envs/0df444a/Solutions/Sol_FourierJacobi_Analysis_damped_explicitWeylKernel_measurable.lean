-- Prove2me | solution 1 for FourierJacobi.Analysis.damped_explicitWeylKernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:57.12241+00:00
-- url     : https://prove2.me/submissions/ee0fd0fa-c100-4e47-97fd-ffa69c1bcd20

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelHeight_measurable


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b T : ℂ) :
    Measurable (fun p : KernelPoint K =>
      T ^ (kernelHeight K p) * explicitWeylKernel K t a b p) :=
  ((measurable_of_countable (fun n : ℤ => T ^ n)).comp
    (kernelHeight_measurable K)).mul (explicitWeylKernel_measurable K t a b)
end FourierJacobi.Analysis
