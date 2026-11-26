-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_entry_minimum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:26.613279+00:00
-- url     : https://prove2.me/submissions/50e070a5-d4fe-4bc0-a86b-cff770dd9668

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernel_localFieldValuation_measurable
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum


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
theorem _root_.solution {α : Type*} [MeasurableSpace α]
    (a x y z : α → K) (ha : Measurable a) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (g (a p) (x p) (y p) (z p))) := by
  simp_rw [actual_entry_minimum]
  unfold entryListMinimum
  have hv := kernel_localFieldValuation_measurable K
  have hzero : Measurable (fun _ : α => (0 : WithTop ℤ)) := measurable_const
  have h0 := (hzero.min (hv.comp ha)).min (hv.comp ha.inv)
  have h1 := (h0.min (hv.comp (ha.mul hx))).min (hv.comp hy)
  exact (h1.min (hv.comp (ha.mul hy))).min (hv.comp hz)
end FourierJacobi.Valuations
