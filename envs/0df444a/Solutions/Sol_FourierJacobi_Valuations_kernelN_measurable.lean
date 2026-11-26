-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelN_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:14.51786+00:00
-- url     : https://prove2.me/submissions/3ff9e516-49d6-4ff4-8fb8-0b12941d3ecb

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernelEntryIndex_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelMinorIndex_measurable

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
theorem _root_.solution : Measurable (kernelN K) :=
  (kernelEntryIndex_measurable K).sub (kernelMinorIndex_measurable K)
end FourierJacobi.Valuations
