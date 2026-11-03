-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:35:07.638958+00:00
-- url     : https://prove2.me/submissions/16a484f8-925e-41de-ad65-c96770e3946d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinMeas : Measurable (ruinTime X x D))
    (hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D)) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) := by
  refine ⟨(fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal), ?_, ?_, ?_⟩
  · intro ω
    rfl
  · exact avram_wave7_08_actual_truncated_clock_real_measurable_of_source X x D n hRuinMeas
  · exact avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping X x D n hRuinStop
