-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:21:22.046381+00:00
-- url     : https://prove2.me/submissions/24805f64-da8a-4bba-937c-44f3aa18d901

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
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
    (H : ℝ≥0) :
    Integrable (fun ω =>
      if (H : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (H : ℝ))) *
          w (x + X.X H ω - rightLimit D H ω))
      else 0) P := by
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (H : WithTop ℝ≥0)) :=
    isStoppingTime_const 𝓕.rightCont H
  simpa only [] using
    (avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
      X hX hBV q hq w hw_cont hw_neg x C D hD H (fun _ => H)
      hStop (by intro ω; exact le_refl _))
