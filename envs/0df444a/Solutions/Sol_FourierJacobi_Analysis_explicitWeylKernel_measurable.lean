-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitWeylKernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:30.03937+00:00
-- url     : https://prove2.me/submissions/34fbc1b7-481e-4bed-a84a-6e763c2161c6

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Valuations_kernelB_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelN_measurable


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b : ℂ) :
    Measurable (explicitWeylKernel K t a b) := by
  have hi : Measurable (fun p : ℤ × ℤ => weylKernelAtIndices t a b p.1 p.2) :=
    measurable_of_countable _
  exact hi.comp ((kernelN_measurable K).prodMk (kernelB_measurable K))
end FourierJacobi.Analysis
