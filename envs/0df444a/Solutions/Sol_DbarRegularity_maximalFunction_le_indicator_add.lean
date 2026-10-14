-- Prove2me | solution 1 for DbarRegularity.maximalFunction_le_indicator_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:44:05.23785+00:00
-- url     : https://prove2.me/submissions/4df469c9-4686-4282-8f73-ba135ea5aca0

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Truncation: `M f ≤ M (f · 1_{|f| > β}) + β` pointwise. -/
theorem maximalFunction_le_indicator_add (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (β : ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ maximalFunction ({y | β < ‖f y‖ₑ}.indicator f) x + β := by
  refine iSup₂_le fun r hr => ?_
  have h0 : volume (ball x r) ≠ 0 := (measure_ball_pos _ _ hr).ne'
  have ht : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  set g := {y | β < ‖f y‖ₑ}.indicator f
  have hpt : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ + β := by
    intro y
    by_cases hy : β < ‖f y‖ₑ
    · rw [show g y = f y from indicator_of_mem (s := {y | β < ‖f y‖ₑ}) hy f]
      exact le_self_add
    · exact (not_lt.1 hy).trans le_add_self
  calc (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
      ≤ (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, (‖g y‖ₑ + β) :=
        mul_le_mul_right (lintegral_mono hpt) _
    _ = (volume (ball x r))⁻¹ * (∫⁻ y in ball x r, ‖g y‖ₑ) + β := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_add,
          mul_comm β, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ maximalFunction g x + β := by
        have hle : (volume (ball x r))⁻¹ * ∫⁻ z in ball x r, ‖g z‖ₑ ≤ maximalFunction g x :=
          le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) =>
            (volume (ball x r))⁻¹ * ∫⁻ z in ball x r, ‖g z‖ₑ) r hr le_rfl
        exact add_le_add hle le_rfl

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (β : ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ maximalFunction ({y | β < ‖f y‖ₑ}.indicator f) x + β :=
  maximalFunction_le_indicator_add d f β x
