-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:03.906813+00:00
-- url     : https://prove2.me/submissions/59dbb29d-055b-4474-9591-db0e96bbc366

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
omit [MeasurableSpace E] in
/-- Source: local Hilbert-geometry helper using Mathlib's `toDual_gradient` and the
norm-preserving Riesz map `InnerProductSpace.toDual`. -/
theorem FunctionalInequalities.Poincare.SmoothTest.norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ E).norm_map _
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
omit [MeasurableSpace E] [BorelSpace E] in
/-- Everywhere the cutoff gradient is dominated by `2‖∇f‖² + 2 (M/R)² f²`. -/
theorem solution {R M : ℝ} (hR : 0 < R)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.bump (E := E))) x‖ ≤ M)
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    ‖gradient (fun y => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 ≤
      2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
    rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.gradient_scaled_mul hf]
    have hs_nonneg :
        0 ≤ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x :=
      FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg R x
    have hs_le_one :
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x ≤ 1 :=
      FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one R x
    have hM0 : 0 ≤ M := by
      exact le_trans (norm_nonneg _) (hM (0 : E))
    have hq : 0 ≤ M / R := div_nonneg hM0 hR.le
    have hgrad :
        ‖gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
          M / R := by
      calc
        ‖gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖ =
            ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖ :=
          (FunctionalInequalities.Poincare.SmoothTest.norm_fderiv_eq_norm_gradient
            (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x).symm
        _ ≤ R⁻¹ * M :=
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_fderiv_scaled_le hR hM x
        _ = M / R := by
          rw [inv_mul_eq_div]
    have ha :
        ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x • gradient f x‖ ≤
          ‖gradient f x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_nonneg]
      calc
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * ‖gradient f x‖ ≤
            1 * ‖gradient f x‖ :=
          mul_le_mul_of_nonneg_right hs_le_one (norm_nonneg _)
        _ = ‖gradient f x‖ := by ring
    have hb :
        ‖f x • gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
          (M / R) * |f x| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |f x| * ‖gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
            |f x| * (M / R) :=
          mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)
        _ = (M / R) * |f x| := by ring
    let A : ℝ := ‖gradient f x‖
    let B : ℝ := (M / R) * |f x|
    let N : ℝ :=
      ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x • gradient f x +
          f x • gradient (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x‖
    have hsum : N ≤ A + B := by
      dsimp [N, A, B]
      exact le_trans (norm_add_le _ _) (add_le_add ha hb)
    have hA : 0 ≤ A := by
      dsimp [A]
      exact norm_nonneg _
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hq (abs_nonneg _)
    have hN : 0 ≤ N := by
      dsimp [N]
      exact norm_nonneg _
    have hsq : N ^ 2 ≤ (A + B) ^ 2 := by
      have h₁ : 0 ≤ A + B - N := sub_nonneg.mpr hsum
      have h₂ : 0 ≤ A + B + N := by linarith
      have h₃ : 0 ≤ (A + B - N) * (A + B + N) :=
        mul_nonneg h₁ h₂
      nlinarith
    have hquad :
        (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
      dsimp [B]
      nlinarith [sq_nonneg (A - (M / R) * |f x|), sq_abs (f x)]
    calc
      N ^ 2 ≤ (A + B) ^ 2 := hsq
      _ ≤ 2 * A ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := hquad
      _ = 2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
        rfl
