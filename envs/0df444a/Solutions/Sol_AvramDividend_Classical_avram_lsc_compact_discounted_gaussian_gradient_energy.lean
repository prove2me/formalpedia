-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_compact_discounted_gaussian_gradient_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:44:36.823191+00:00
-- url     : https://prove2.me/submissions/d952b75f-7d73-4e5c-a829-94a879d17525

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Compact localisation controls the discounted Brownian gradient's
quadratic energy on every finite physical time horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q σ : ℝ) (hq : 0 ≤ q)
    (U : Ω → ℝ → ℝ)
    (hU : ∀ ω s, 0 ≤ s → U ω s ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
          (‖(if 0 ≤ s then
              Real.exp (-(q * s)) * deriv w (U ω s) * σ
            else 0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hDeriv⟩ :=
    avram_p4_f3_source_interior_compact_derivative_bound
      w C hw_smooth hopen a b hband
  let K : ℝ := max B 0 * |σ|
  have hK : 0 ≤ K :=
    mul_nonneg (le_max_right B 0) (abs_nonneg σ)
  have hBound : ∀ ω s,
      |(if 0 ≤ s then
          Real.exp (-(q * s)) * deriv w (U ω s) * σ
        else 0 : ℝ)| ≤ K := by
    intro ω s
    by_cases hs : 0 ≤ s
    · simp only [if_pos hs]
      have hjet : |deriv w (U ω s)| ≤ max B 0 :=
        (hDeriv _ (hU ω s hs)).trans (le_max_left B 0)
      have he : Real.exp (-(q * s)) ≤ 1 := by
        calc
          Real.exp (-(q * s)) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hq hs])
          _ = 1 := Real.exp_zero
      have he0 : 0 ≤ Real.exp (-(q * s)) :=
        (Real.exp_pos _).le
      calc
        |Real.exp (-(q * s)) * deriv w (U ω s) * σ|
            = Real.exp (-(q * s)) * |deriv w (U ω s)| * |σ| := by
                rw [abs_mul, abs_mul, abs_of_nonneg he0]
        _ ≤ 1 * |deriv w (U ω s)| * |σ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right he (abs_nonneg _))
            (abs_nonneg σ)
        _ ≤ 1 * max B 0 * |σ| := by
          gcongr <;> exact hjet
        _ = K := by simp [K]
    · simpa [if_neg hs] using hK
  refine ⟨K, hK, ?_⟩
  intro T hT
  exact avram_lsc_finite_horizon_bounded_integrand_energy
    (fun ω s => if 0 ≤ s then
      Real.exp (-(q * s)) * deriv w (U ω s) * σ
     else 0)
    K hK hBound T hT

