-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_indices_of_minima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:24.528985+00:00
-- url     : https://prove2.me/submissions/d1ae56a8-b70a-4f9b-b5e6-151389cf94a2

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
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
theorem _root_.solution (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    (kernelEll K p, kernelB K p) = cartanIndices r k j h c := by
  have he' : kernelEntryIndex K p = entryMinimum r k j h := by
    apply WithTop.coe_injective
    exact (actualEntryInteger_coe _ _ _ _ _).trans he
  have hm' : kernelMinorIndex K p = minorMinimum r k j h c := by
    apply WithTop.coe_injective
    exact (actualMinorInteger_coe _ _ _ _ _).trans hm
  unfold kernelEll kernelN kernelB cartanIndices
  rw [he',hm']
  simp only [Prod.mk.injEq]
  constructor
  · ring
  · trivial
end FourierJacobi.Valuations
