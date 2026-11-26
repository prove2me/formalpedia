-- Prove2me | solution 1 for FourierJacobi.Analysis.weylKernelAtIndices_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:57.181778+00:00
-- url     : https://prove2.me/submissions/a579487f-5bca-497a-8078-22ce03594380

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
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
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b T : ℂ) (n B : ℤ) (hT : T ≠ 0) :
    T ^ (n+B) * weylKernelAtIndices t a b n B =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6*n+4*B) *
          (T * weylU a b i) ^ n * (T * weylV a b i) ^ B := by
  unfold weylKernelAtIndices
  calc
    _ = (poincare t)⁻¹ * ∑ i : Fin 8,
        T ^ (n+B) * (weylWeights t a b i * t ^ (6*n+4*B) *
          (weylU a b i) ^ n * (weylV a b i) ^ B) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [zpow_add₀ hT]
      simp only [mul_zpow]
      ring
end FourierJacobi.Analysis
