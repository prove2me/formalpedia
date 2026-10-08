-- Prove2me | solution 1 for AvramDividend.Classical.finite_Iic_of_positive_laplace_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:18:54.382135+00:00
-- url     : https://prove2.me/submissions/8be85b84-a6d6-4323-a6b3-e7c1d0915158

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (β : Measure ℝ) (s x : ℝ) (hs : 0 < s)
    (hLap :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) ≠ ∞) :
    β (Iic x) ≠ ∞ := by
  let f : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-s * z))
  let ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-s * x))
  have hf : AEMeasurable f β := by
    dsimp [f]
    fun_prop
  have hε0 : ε ≠ 0 := by
    dsimp [ε]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hεtop : ε ≠ ∞ := by
    dsimp [ε]
    exact ENNReal.ofReal_ne_top
  have hsub : Iic x ⊆ {z : ℝ | ε ≤ f z} := by
    intro z hz
    change z ≤ x at hz
    dsimp [ε, f]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp]
    nlinarith
  have hbound :
      β (Iic x) ≤ (∫⁻ z : ℝ, f z ∂β) / ε :=
    (measure_mono hsub).trans
      (meas_ge_le_lintegral_div hf hε0 hεtop)
  have hdiv :
      (∫⁻ z : ℝ, f z ∂β) / ε ≠ ∞ := by
    apply ENNReal.div_ne_top
    · simpa [f] using hLap
    · exact hε0
  exact ne_top_of_le_ne_top hdiv hbound
