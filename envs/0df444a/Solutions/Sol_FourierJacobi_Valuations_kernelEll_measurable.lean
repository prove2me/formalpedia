-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelEll_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:19.281375+00:00
-- url     : https://prove2.me/submissions/e2c915f8-b98a-4fc4-b6c2-3878e0d2b154

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernelN_measurable

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Valuations.kernelField_t2Space
attribute [local instance] FourierJacobi.Valuations.kernelField_secondCountable
namespace FourierJacobi.Valuations
theorem _root_.solution : Measurable (kernelEll K) :=
  (kernelN_measurable K).const_mul 2
end FourierJacobi.Valuations
