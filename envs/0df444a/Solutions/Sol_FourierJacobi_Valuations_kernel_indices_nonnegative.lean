-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_indices_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:41.420379+00:00
-- url     : https://prove2.me/submissions/f60ce894-5671-4b6f-9473-8d5d57f2e213

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualInteger_bounds
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (p : KernelPoint K) :
    0 ≤ kernelN K p ∧ 0 ≤ kernelB K p ∧ 0 ≤ kernelEll K p ∧ 0 ≤ kernelHeight K p := by
  have h := actualInteger_bounds (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2
  simp only [kernelEll, kernelHeight, kernelN, kernelB, kernelEntryIndex, kernelMinorIndex]
  omega
end FourierJacobi.Valuations
