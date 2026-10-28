-- Prove2me | solution 1 for AvramDividend.Classical.levy_laplace_exponent_convexOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:29:35.602066+00:00
-- url     : https://prove2.me/submissions/351aa0f9-3c06-4f66-82f0-989421109f10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ConvexOn ℝ (Ici (0 : ℝ)) X.ψ := by
  refine ⟨convex_Ici 0, ?_⟩
  intro a ha b hb μ w hμ hw hsum
  set g : ℝ → ℝ → ℝ := fun θ y => Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y
    with hg
  have hint : ∀ θ, 0 ≤ θ → IntegrableOn (g θ) (Iio (0 : ℝ)) X.ν := by
    intro θ hθ
    have := levy_compensated_jump_integrable_nonneg X θ hθ
    convert this using 2; rfl
  have hpt : ∀ y, g (μ * a + w * b) y ≤ μ * g a y + w * g b y := by
    intro y
    have hexp := convexOn_exp.2 (mem_univ (a * y)) (mem_univ (b * y)) hμ hw hsum
    simp only [smul_eq_mul] at hexp
    simp only [hg]
    have h1 : (μ * a + w * b) * y = μ * (a * y) + w * (b * y) := by ring
    rw [h1]
    have : μ * (Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y) +
        w * (Real.exp (b * y) - 1 - b * y * (Ioo (-1 : ℝ) 1).indicator 1 y) =
        (μ * Real.exp (a * y) + w * Real.exp (b * y)) - (μ + w) -
          (μ * (a * y) + w * (b * y)) * (Ioo (-1 : ℝ) 1).indicator 1 y := by ring
    rw [this, hsum]
    linarith
  have hab : 0 ≤ μ * a + w * b := by
    have : (0:ℝ) ≤ a := ha; have : (0:ℝ) ≤ b := hb; positivity
  have hI : ∫ y in Iio (0 : ℝ), g (μ * a + w * b) y ∂X.ν ≤
      μ * ∫ y in Iio (0 : ℝ), g a y ∂X.ν + w * ∫ y in Iio (0 : ℝ), g b y ∂X.ν := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · exact integral_mono (hint _ hab) (((hint a ha).const_mul μ).add ((hint b hb).const_mul w)) hpt
    · exact (hint a ha).const_mul μ
    · exact (hint b hb).const_mul w
  have hsq : (μ * a + w * b) ^ 2 ≤ μ * a ^ 2 + w * b ^ 2 := by
    have := (convexOn_pow 2).2 (show (0:ℝ) ≤ a from ha) (show (0:ℝ) ≤ b from hb) hμ hw hsum
    simpa [smul_eq_mul] using this
  simp only [SpectrallyNegativeLevy.ψ, laplaceExponent, smul_eq_mul]
  change X.c * (μ * a + w * b) + X.σ ^ 2 * (μ * a + w * b) ^ 2 / 2 +
      ∫ y in Iio (0 : ℝ), g (μ * a + w * b) y ∂X.ν ≤
    μ * (X.c * a + X.σ ^ 2 * a ^ 2 / 2 + ∫ y in Iio (0 : ℝ), g a y ∂X.ν) +
    w * (X.c * b + X.σ ^ 2 * b ^ 2 / 2 + ∫ y in Iio (0 : ℝ), g b y ∂X.ν)
  have hs2 : 0 ≤ X.σ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsq hs2]
