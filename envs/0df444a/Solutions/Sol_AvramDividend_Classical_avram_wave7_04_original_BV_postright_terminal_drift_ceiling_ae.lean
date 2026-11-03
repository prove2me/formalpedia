-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:08.890605+00:00
-- url     : https://prove2.me/submissions/1eac097c-5433-434c-8612-b88c8ee250df

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      x + X.X T ω - rightLimit D T ω ≤
        x + (T : ℝ) * X.drift := by
  classical
  have hSource :=
    avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD
  filter_upwards [hSource] with ω hIncrements
  have hClock := hIncrements (0 : ℝ≥0) T (by simp)
  have hXzero : X.X 0 ω = 0 := X.X_zero ω
  simp [hXzero] at hClock
  linarith [hInitial ω]
