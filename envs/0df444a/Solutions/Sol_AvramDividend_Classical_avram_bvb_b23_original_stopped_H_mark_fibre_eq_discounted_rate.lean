-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:06:23.375504+00:00
-- url     : https://prove2.me/submissions/726df27b-1333-43a2-9855-010c052dc92a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original closed-cap marked H fibre is its physical discounted negative-mark rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let good : Prop := 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    (∫ z, (if good ∧ z < 0 then Real.exp (-(q * (t : ℝ))) *
      (w (U t + z) - w (U t)) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ)))) =
    if good then Real.exp (-(q * (t : ℝ))) *
      (∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
    else 0 := by
  intro U good
  by_cases hg : good
  · have hAE : (fun z : ℝ =>
        if good ∧ z < 0 then Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0) =ᵐ[X.ν.restrict (Iio (0 : ℝ))]
        (fun z : ℝ => Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t))) := by
      filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with z hz
      have hzlt : z < 0 := hz
      simp [hg, hzlt]
    rw [integral_congr_ae hAE]
    simp [hg, integral_const_mul]
  · have hzero : (fun z : ℝ =>
        if good ∧ z < 0 then Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0) = (fun _ => (0 : ℝ)) := by
      funext z
      simp [hg]
    simp [hzero, hg]
