-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_one_sided_upperstrip_convolution_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:27:45.554089+00:00
-- url     : https://prove2.me/submissions/3c34e208-f148-436a-b1b5-2f302419b5b0

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set
noncomputable section

theorem solution
    (μ : Measure ℝ) (φ g : ℝ → ℝ)
    (hφI : Integrable φ μ)
    (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε)
    (b y c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ u, g u ≤ if b < u then c else 0)
    (hInt : Integrable (fun z => φ z * g (y - ε*z)) μ) :
    (∫ z, φ z * g (y - ε*z) ∂μ) ≤
      if b < y then c else 0 := by
  have hPoint : ∀ᵐ z ∂μ,
      φ z * g (y - ε*z) ≤ φ z * (if b < y then c else 0) := by
    filter_upwards [hPositive, hφpos] with z hz hφz
    have hmul : 0 < ε * z := mul_pos hε hz
    have hUpper : g (y - ε*z) ≤ if b < y then c else 0 := by
      by_cases hy : b < y
      · simp only [if_pos hy]
        have hB := hg (y - ε*z)
        by_cases hshift : b < y - ε*z
        · simpa only [if_pos hshift] using hB
        · simp only [if_neg hshift] at hB
          linarith
      · have hshift : ¬ b < y - ε*z := by
          linarith
        simpa only [if_neg hy, if_neg hshift] using hg (y - ε*z)
    exact mul_le_mul_of_nonneg_left hUpper hφz
  have hRight : Integrable
      (fun z => φ z * (if b < y then c else 0)) μ :=
    hφI.mul_const _
  have hCompare := integral_mono_ae hInt hRight hPoint
  rw [integral_mul_const, hφnorm, one_mul] at hCompare
  exact hCompare
