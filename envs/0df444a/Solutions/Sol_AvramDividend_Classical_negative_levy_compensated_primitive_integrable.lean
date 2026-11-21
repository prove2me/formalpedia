-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_compensated_primitive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:34:38.386837+00:00
-- url     : https://prove2.me/submissions/13e1b728-12c7-4885-aacd-580fe06a4e07

import Mathlib
import Theorems.Thm_AvramDividend_Classical_compensated_jump_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_compensated_primitive_quadratic_large_mark_pointwise
import Theorems.Thm_AvramDividend_Classical_negative_levy_quadratic_large_mark_envelope_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ =>
      ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν := by
  let F : ℝ → ℝ := fun y =>
    ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)
  let B : ℝ → ℝ := fun y =>
    θ / 2 * min 1 (y ^ 2) +
      |(Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y|
  have hB : Integrable B ν :=
    negative_levy_quadratic_large_mark_envelope_integrable ν hQuad hLarge θ
  have hEq : F = fun y : ℝ =>
      (Real.exp (-θ * (-y)) - 1 + θ * (-y)) / θ := by
    funext y
    exact compensated_jump_exponential_primitive θ (-y) hθ
  have hMeas : AEStronglyMeasurable F ν := by
    rw [hEq]
    exact (by fun_prop : Measurable
      (fun y : ℝ => (Real.exp (-θ * (-y)) - 1 + θ * (-y)) / θ)).aestronglyMeasurable
  have hAE : ∀ᵐ y ∂ν, 0 ≤ F y ∧ F y ≤ B y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    have hneg : y < 0 := lt_of_not_ge (by simpa only [mem_Ici] using hy)
    exact compensated_primitive_quadratic_large_mark_pointwise θ y hθ.le hneg
  exact integrable_of_le_of_le hMeas
    (hAE.mono (fun _ h => h.1)) (hAE.mono (fun _ h => h.2))
    (integrable_zero ℝ ℝ ν) hB
