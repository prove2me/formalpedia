-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weight_retains_infinite_origin_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:30:44.377236+00:00
-- url     : https://prove2.me/submissions/88e06d5d-db68-4c52-8167-94cdf2f0dd05

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (μ : Measure ℝ)
    (φ : ℝ) (hφ : 0 ≤ φ)
    (hinf : μ (Ioc (0 : ℝ) 1) = ⊤) :
    (μ.withDensity (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(φ * t))))) (Ioc (0 : ℝ) 1) = ⊤ := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-φ))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hlow : ∀ t ∈ Ioc (0 : ℝ) 1,
      c ≤ ENNReal.ofReal (Real.exp (-(φ * t))) := by
    intro t ht
    have hmul : φ * t ≤ φ := by
      calc
        φ * t ≤ φ * 1 := mul_le_mul_of_nonneg_left ht.2 hφ
        _ = φ := mul_one φ
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by linarith))
  have hmono : (∫⁻ t in Ioc (0 : ℝ) 1, c ∂μ) ≤
      (∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (Real.exp (-(φ * t))) ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hlow t ht
  have hconst : (∫⁻ t in Ioc (0 : ℝ) 1, c ∂μ) = ⊤ := by
    simp [lintegral_const, hinf, hc.ne']
  rw [withDensity_apply _ measurableSet_Ioc]
  exact top_unique (by simpa only [hconst] using hmono)
