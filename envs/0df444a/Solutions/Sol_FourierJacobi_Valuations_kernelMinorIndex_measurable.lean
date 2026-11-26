-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelMinorIndex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:05.949823+00:00
-- url     : https://prove2.me/submissions/f19f04e4-1598-4f72-97ec-1205aeb50847

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernel_minor_minimum_measurable
import Theorems.Thm_FourierJacobi_Valuations_actual_minima_finite


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
theorem _root_.solution : Measurable (kernelMinorIndex K) := by
  have ha : Measurable (fun p : KernelPoint K => (p.1 : K)) :=
    (show Measurable (fun a : Kˣ => (a : K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hm := kernel_minor_minimum_measurable K
    (fun p : KernelPoint K => (p.1 : K)) (fun p => p.2.1)
    (fun p => p.2.2.1) (fun p => p.2.2.2)
    ha measurable_snd.fst measurable_snd.snd.fst measurable_snd.snd.snd
    (fun p => Units.ne_zero p.1)
  have he : kernelMinorIndex K = (fun p : KernelPoint K =>
      (matrixMinimum (localFieldValuation K)
        (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2))).untopA) := by
    funext p
    exact (WithTop.untopA_eq_untop
      (actual_minima_finite _ _ _ _ _ (Units.ne_zero p.1)).2).symm
  rw [he]
  exact hm.untopA
end FourierJacobi.Valuations
