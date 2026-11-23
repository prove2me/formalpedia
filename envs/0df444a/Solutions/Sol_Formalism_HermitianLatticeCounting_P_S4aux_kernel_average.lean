-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.kernel_average
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:13.392367+00:00
-- url     : https://prove2.me/submissions/4a8ac597-eca3-4ede-a4c9-fb3b23c5be82

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : KernelAvg := by
  intro ι _ μ M ω e1 e2 hμ hrev hrow hM
  have key : ∑ i, (μ i : ℂ) * ω i = ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j - ∑ i, (μ i : ℂ) * ω i * (((∑ j, M i j) - 1 : ℝ) : ℂ) := by
    have : ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j = ∑ i, (μ i : ℂ) * ω i * ((∑ j, M i j : ℝ) : ℂ) := by
      simp only [Finset.mul_sum, Complex.ofReal_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have := congrArg (fun t : ℝ => (t : ℂ)) (hrev j i)
      simp only [Complex.ofReal_mul] at this
      linear_combination ω i * this
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [key]
  calc _ ≤ ‖∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j‖ + ‖∑ i, (μ i : ℂ) * ω i * (((∑ j, M i j) - 1 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ∑ i, μ i * (e2 * ‖ω i‖) + ∑ i, μ i * ‖ω i‖ * e1 := by
        gcongr
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          exact mul_le_mul_of_nonneg_left (hM i) (hμ i)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          exact mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hμ i) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
end Formalism.HermitianLatticeCounting.P.S4aux
