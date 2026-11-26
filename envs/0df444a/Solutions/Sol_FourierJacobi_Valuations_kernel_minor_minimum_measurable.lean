-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_minor_minimum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:28.682873+00:00
-- url     : https://prove2.me/submissions/28803556-f43f-44b8-867d-0732dd024a97

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernel_localFieldValuation_measurable
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum


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
    (hy : Measurable y) (hz : Measurable z) (ha0 : ∀ p, a p ≠ 0) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (secondCompound (g (a p) (x p) (y p) (z p)))) := by
  have he : (fun p => matrixMinimum (localFieldValuation K)
      (secondCompound (g (a p) (x p) (y p) (z p)))) =
      (fun p => minorListMinimum (localFieldValuation K) (a p) (x p) (y p) (z p)) :=
    funext fun p => actual_minor_minimum _ _ _ _ _ (ha0 p)
  rw [he]
  unfold minorListMinimum
  have hv := kernel_localFieldValuation_measurable K
  have hzero : Measurable (fun _ : α => (0 : WithTop ℤ)) := measurable_const
  have h0 := (hzero.min (hv.comp ha)).min (hv.comp ha.inv)
  have h1 := (h0.min (hv.comp (ha.mul hx))).min (hv.comp hy)
  have h2 := (h1.min (hv.comp (ha.mul hy))).min (hv.comp (ha.mul hz))
  exact (h2.min (hv.comp (hz.div ha))).min
    (hv.comp (ha.mul ((hy.pow_const 2).sub (hx.mul hz))))
end FourierJacobi.Valuations
