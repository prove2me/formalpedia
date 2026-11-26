-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitWeylKernel_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:45.449949+00:00
-- url     : https://prove2.me/submissions/f59c562f-c16b-48b5-85a8-1238e8abf124

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_kernel_half_ell
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b : ℂ) (p : KernelPoint K) :
    explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (3 * kernelEll K p + 4 * kernelB K p) *
          (weylU a b i) ^ (kernelEll K p / 2) *
            (weylV a b i) ^ (kernelB K p) := by
  rw [kernel_half_ell]
  unfold explicitWeylKernel weylKernelAtIndices kernelEll
  simp only [Function.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 3
  ring
end FourierJacobi.Analysis
