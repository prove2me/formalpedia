-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.kernel_average_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:13.123192+00:00
-- url     : https://prove2.me/submissions/0ca74b4d-6795-41aa-b6cc-85bdc1700811

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
theorem _root_.solution : KernelAvgSum := by
  intro ι μ M ω e1 e2 hμ hμs hM hMs hrev hω hrow hker
  obtain ⟨R, hR⟩ : ∃ R : ι → ℝ, ∀ i, R i = ∑' j, M i j := ⟨_, fun _ => rfl⟩
  simp only [← hR] at hrow
  have hRle : ∀ i, R i ≤ 1 + e1 := fun i => by have := abs_le.1 (hrow i); linarith [this.2]
  have hR0 : ∀ i, 0 ≤ R i := fun i => by rw [hR]; exact tsum_nonneg (hM i)
  have hμR : Summable fun i => μ i * R i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hμ i) (hR0 i))
      (fun i => mul_le_mul_of_nonneg_left (hRle i) (hμ i)) (hμs.mul_right (1 + e1))
  have hS : Summable (fun p : ι × ι => μ p.1 * M p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (hμ _) (hM _ _))]
    refine ⟨fun i => (hMs i).mul_left (μ i), ?_⟩
    have : (fun i => ∑' j, μ i * M i j) = fun i => μ i * R i := by
      ext i; rw [hR]; exact tsum_mul_left
    simpa only [this] using hμR
  have hF : Summable (Function.uncurry fun i j => ((μ i * M i j : ℝ) : ℂ) * ω j) := by
    apply Summable.of_norm
    refine hS.congr ?_
    rintro ⟨i, j⟩
    simp only [Function.uncurry, norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [← abs_mul, abs_of_nonneg (mul_nonneg (hμ _) (hM _ _))]
  have hA : ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j = ∑' i, ((μ i * R i : ℝ) : ℂ) * ω i := by
    calc ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j
        = ∑' i, ∑' j, ((μ i * M i j : ℝ) : ℂ) * ω j := by
          refine tsum_congr fun i => ?_
          rw [← tsum_mul_left]
          refine tsum_congr fun j => ?_
          push_cast; ring
      _ = ∑' j, ∑' i, ((μ i * M i j : ℝ) : ℂ) * ω j := (hF.tsum_comm).symm
      _ = _ := by
          refine tsum_congr fun j => ?_
          rw [tsum_mul_right]
          congr 1
          rw [← Complex.ofReal_tsum]
          congr 1
          rw [hR, ← tsum_mul_left]
          exact tsum_congr fun i => hrev i j
  have s1 : Summable fun i => ((μ i * R i : ℝ) : ℂ) * ω i := by
    apply Summable.of_norm
    refine hμR.congr fun i => ?_
    rw [norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hμ _) (hR0 _))]
  have s2 : Summable fun i => (μ i : ℂ) * ω i := by
    apply Summable.of_norm
    refine hμs.congr fun i => ?_
    rw [norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have key : ∑' i, (μ i : ℂ) * ω i
      = ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j - ∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ) := by
    have s3 : Summable fun i => (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ) := by
      refine (s1.sub s2).congr fun i => ?_
      push_cast; ring
    rw [hA, ← (s1.tsum_sub s3)]
    refine tsum_congr fun i => ?_
    push_cast; ring
  rw [key]
  have b1 : ‖∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j‖ ≤ (∑' i, μ i) * e2 := by
    refine tsum_of_norm_bounded (hμs.hasSum.mul_right e2) fun i => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
    exact mul_le_mul_of_nonneg_left (hker i) (hμ i)
  have b2 : ‖∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ)‖ ≤ (∑' i, μ i) * e1 := by
    refine tsum_of_norm_bounded (hμs.hasSum.mul_right e1) fun i => ?_
    rw [norm_mul, norm_mul, hω, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hμ _)]
    exact mul_le_mul_of_nonneg_left (hrow i) (hμ i)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (∑' i, μ i) * e2 + (∑' i, μ i) * e1 := add_le_add b1 b2
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P.S4aux
