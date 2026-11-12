-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_K_exact_real_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:18:34.956004+00:00
-- url     : https://prove2.me/submissions/3f7862ee-6e4b-4622-ad94-d35b6e48c27d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_compensator_K_real_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped H compensator K equals the real-time closed-cap rate integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (n : ℕ) (ω : Ω) :
    let U : ℝ≥0 → Ω → ℝ := fun r η => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z η - rightLimit D z η) r
    let good : ℝ≥0 → Prop := fun t =>
      0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C
    let H : (ℝ≥0 × Ω) × ℝ → ℝ := fun p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0
      then Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))
      else 0
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    AEStronglyMeasurable
      (fun t : ℝ≥0 => ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) →
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T,
      if good (Real.toNNReal t)
      then Real.exp (-(q * ((Real.toNNReal t : ℝ≥0) : ℝ))) *
        ψ (U (Real.toNNReal t) ω)
      else 0) := by
  intro U good H ψ hMeas
  rw [avram_bvb_b22_original_compensator_K_real_time_integral
    X T ω H hMeas]
  apply integral_congr_ae
  filter_upwards [] with t
  simpa only [U, good, H, ψ, and_assoc] using
    (avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
      X x C D w q T n ω (Real.toNNReal t))
