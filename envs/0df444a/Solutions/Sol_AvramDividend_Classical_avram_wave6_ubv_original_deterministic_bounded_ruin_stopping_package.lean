-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:57:46.305809+00:00
-- url     : https://prove2.me/submissions/5af41d74-5d68-480d-8c97-a980b5143305

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ n ω, min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (n : ℝ≥0∞)) ∧
    (∀ ω, Monotone
      (fun n : ℕ => min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω, (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
      ruinTime X x D ω) := by
  have hst : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hclock := avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
    X x D hD.1.1
  refine ⟨?_, ?_, hclock.2.1, hclock.2.2⟩
  · intro n
    exact hst.min_const (n : ℝ≥0)
  · intro n ω
    exact min_le_right _ _
end
