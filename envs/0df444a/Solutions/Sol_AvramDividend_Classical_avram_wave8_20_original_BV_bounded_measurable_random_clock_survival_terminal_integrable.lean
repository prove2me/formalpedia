-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:16:34.8292+00:00
-- url     : https://prove2.me/submissions/e90d85ee-5ef7-4f2c-9572-63ff92b5633c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ)
    (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by
  classical
  haveI : IsProbabilityMeasure P := X.isProbability
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hJoint :=
    avram_wave8_20_original_strict_survival_terminal_joint_measurable
      X x D hStrat w hw_cont hw_neg q
  have hMeas : Measurable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) := by
    simpa only [Function.comp_def, id_eq] using
      hJoint.comp (hτMeas.prodMk measurable_id)
  obtain ⟨K, hK0, hBound⟩ :=
    avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
      X hX hBV q hq w hw_cont x C D hD H τ hτBound
  apply Integrable.of_bound hMeas.aestronglyMeasurable K
  filter_upwards [hBound] with ω hω
  have hn : 0 ≤
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) := by
    split_ifs
    · exact le_max_left _ _
    · exact le_refl _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hω
