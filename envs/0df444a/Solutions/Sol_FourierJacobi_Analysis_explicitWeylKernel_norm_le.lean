-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitWeylKernel_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:50.973813+00:00
-- url     : https://prove2.me/submissions/c41f875e-bddd-4e7c-9408-e1ce2ced7399

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Analysis_weylKernelAtIndices_norm_le
import Theorems.Thm_FourierJacobi_Analysis_poincare_coe_norm
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
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
theorem _root_.solution (t : ℝ) (a b : ℂ) (p : KernelPoint K)
    (ht : 0 ≤ t) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (t : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (t : ℂ) a b i‖) / poincare t) *
        t ^ (3 * kernelEll K p + 4 * kernelB K p) := by
  have hn := weylKernelAtIndices_norm_le (t : ℂ) a b (kernelN K p) (kernelB K p) ha hb
  have he : 6 * kernelN K p + 4 * kernelB K p =
      3 * kernelEll K p + 4 * kernelB K p := by unfold kernelEll; ring
  simpa only [explicitWeylKernel, Function.comp_apply, poincare_coe_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, he] using hn
end FourierJacobi.Analysis
