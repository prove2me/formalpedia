-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelEntryIndex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:14.9438+00:00
-- url     : https://prove2.me/submissions/a01ea1ea-5bda-4c79-a1a2-f90c058a74ea

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_kernel_entry_minimum_measurable
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
theorem _root_.solution : Measurable (kernelEntryIndex K) := by
  have ha : Measurable (fun p : KernelPoint K => (p.1 : K)) :=
    (show Measurable (fun a : Kˣ => (a : K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hm := kernel_entry_minimum_measurable K
    (fun p : KernelPoint K => (p.1 : K)) (fun p => p.2.1)
    (fun p => p.2.2.1) (fun p => p.2.2.2)
    ha measurable_snd.fst measurable_snd.snd.fst measurable_snd.snd.snd
  have he : kernelEntryIndex K = (fun p : KernelPoint K =>
      (matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2)).untopA) := by
    funext p
    exact (WithTop.untopA_eq_untop
      (actual_minima_finite _ _ _ _ _ (Units.ne_zero p.1)).1).symm
  rw [he]
  exact hm.untopA
end FourierJacobi.Valuations
