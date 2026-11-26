-- Prove2me | solution 1 for FourierJacobi.Analysis.weylKernelAtIndices_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:46.353536+00:00
-- url     : https://prove2.me/submissions/9d9c2ec7-5d40-425d-92a6-b8bff09a3c2f

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b : ℂ) (n B : ℤ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖weylKernelAtIndices t a b n B‖ ≤
      ((∑ i : Fin 8, ‖weylWeights t a b i‖) / ‖poincare t‖) *
        ‖t‖ ^ (6 * n + 4 * B) := by
  unfold weylKernelAtIndices
  rw [norm_mul, norm_inv]
  calc
    _ ≤ ‖poincare t‖⁻¹ * ∑ i : Fin 8,
        ‖weylWeights t a b i * t ^ (6*n+4*B) *
          (weylU a b i) ^ n * (weylV a b i) ^ B‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by
      simp_rw [norm_mul, norm_zpow, weylU_unitary ha hb, weylV_unitary ha hb,
        one_zpow, mul_one]
      rw [← Finset.sum_mul]
      ring
end FourierJacobi.Analysis
