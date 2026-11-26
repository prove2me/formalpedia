-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelHeight_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:28.644801+00:00
-- url     : https://prove2.me/submissions/b695ae19-9ad0-457e-b0e7-5d1af5d96ec9

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernelN_measurable
import Theorems.Thm_FourierJacobi_Valuations_kernelB_measurable

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
theorem _root_.solution : Measurable (kernelHeight K) :=
  (kernelN_measurable K).add (kernelB_measurable K)
end FourierJacobi.Valuations
