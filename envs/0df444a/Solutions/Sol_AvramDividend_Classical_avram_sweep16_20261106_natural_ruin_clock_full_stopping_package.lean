-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:27:16.988851+00:00
-- url     : https://prove2.me/submissions/f1bf0b4b-909e-4b90-9334-52ed7a305cdc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ, 0 < n →
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) ∧
      (∀ ω, (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
        ruinTime X x D ω) := by
  intro n _hn
  obtain ⟨_hEq, hBound, hRuin⟩ :=
    avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  refine ⟨hBound, ?_, hRuin⟩
  exact avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
    X x D n (ruinTime_stopping_rightCont_filtration X x D hD.1.1)
