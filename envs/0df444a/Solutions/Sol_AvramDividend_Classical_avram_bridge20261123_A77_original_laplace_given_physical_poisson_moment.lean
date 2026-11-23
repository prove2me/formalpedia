-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:48:45.520349+00:00
-- url     : https://prove2.me/submissions/0d40c979-aa80-4fe4-846a-2f8885a0f526

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_compound_poisson_laplace_from_mark_moment
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hModel :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  rcases hModel with ⟨N, r, m, hLaw, hMoment, hRate⟩
  have hMark :
      (∫ ω, Real.exp ((1 : ℝ) *
          ((θ * J ω + (r : ℝ)) - (r : ℝ))) ∂P) =
        ∫ ω, m ^ (N ω) ∂P := by
    simpa only [add_sub_cancel_right, one_mul] using hMoment
  have hCP :=
    AvramDividend.Classical.chat06_compound_poisson_laplace_from_mark_moment
      N (fun ω => θ * J ω + (r : ℝ)) r (1 : ℝ) m hLaw hMark
  have hCP' :
      (∫ ω, Real.exp (θ * J ω + (r : ℝ)) ∂P) =
        Real.exp ((r : ℝ) * m) := by
    convert hCP using 1
    · simp only [one_mul]
    · congr 1
      ring
  have hFactor :
      (∫ ω, Real.exp (θ * J ω + (r : ℝ)) ∂P) =
        (∫ ω, Real.exp (θ * J ω) ∂P) *
          Real.exp (r : ℝ) := by
    simp_rw [Real.exp_add]
    rw [integral_mul_const]
  rw [hFactor] at hCP'
  have hExp :
      Real.exp ((r : ℝ) * m) =
        Real.exp ((r : ℝ) * (m - 1)) * Real.exp (r : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp] at hCP'
  have hResult :
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        Real.exp ((r : ℝ) * (m - 1)) := by
    exact mul_right_cancel₀ (Real.exp_ne_zero _) hCP'
  rw [hRate] at hResult
  exact hResult
