-- Prove2me | solution 1 for DbarRegularity.maximalFunction_le_eLpNorm_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:41:46.917986+00:00
-- url     : https://prove2.me/submissions/ed42da24-bcc3-42e0-ba52-9af3c4f2cd9e

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- The maximal function is bounded pointwise by the essential supremum of `‖f‖`. -/
theorem maximalFunction_le_eLpNorm_top (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ eLpNorm f ⊤ volume := by
  refine iSup₂_le fun r hr => ?_
  have h0 : volume (ball x r) ≠ 0 := (measure_ball_pos _ _ hr).ne'
  have ht : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have hae : ∀ᵐ y ∂volume.restrict (ball x r), ‖f y‖ₑ ≤ eLpNorm f ⊤ volume := by
    rw [eLpNorm_exponent_top]
    exact ae_restrict_of_ae ae_le_eLpNormEssSup
  calc (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
      ≤ (volume (ball x r))⁻¹ * ∫⁻ _ in ball x r, eLpNorm f ⊤ volume := by
        exact mul_le_mul_right (lintegral_mono_ae hae) _
    _ = eLpNorm f ⊤ volume := by
        rw [setLIntegral_const, mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 ht, mul_one]

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ eLpNorm f ⊤ volume :=
  maximalFunction_le_eLpNorm_top d f x
