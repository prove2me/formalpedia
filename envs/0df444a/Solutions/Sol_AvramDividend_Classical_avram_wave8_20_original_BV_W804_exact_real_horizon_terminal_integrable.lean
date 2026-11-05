-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_W804_exact_real_horizon_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:19:49.661204+00:00
-- url     : https://prove2.me/submissions/7ab6919f-b493-4e57-aa30-f83296934d2e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
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
    (T : ℝ) (hT : 0 ≤ T) :
    let H : ℝ≥0 := ⟨T, hT⟩
    Integrable (fun ω =>
      if (H : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X H ω - rightLimit D H ω))
      else 0) P := by
  dsimp
  let H : ℝ≥0 := ⟨T, hT⟩
  have hH : (H : ℝ) = T := rfl
  have hInt : Integrable (fun ω =>
      if (H : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (H : ℝ))) *
          w (x + X.X H ω - rightLimit D H ω))
      else 0) P :=
    avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
      X hX hBV q hq w hw_cont hw_neg x C D hD H
  rw [hH] at hInt
  exact hInt
