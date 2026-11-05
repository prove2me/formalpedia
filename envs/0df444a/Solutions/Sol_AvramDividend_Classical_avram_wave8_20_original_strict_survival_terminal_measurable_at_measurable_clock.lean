-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_measurable_at_measurable_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:02:35.67585+00:00
-- url     : https://prove2.me/submissions/9cc23a57-6842-4d25-bde2-b9081f1941c7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 2000000

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) := by
  have hpair : Measurable (fun ω : Ω => (τ ω, ω)) :=
    hτ.prodMk measurable_id
  exact (avram_wave8_20_original_strict_survival_terminal_joint_measurable
    X x D hD w hw_cont hw_neg q).comp hpair
