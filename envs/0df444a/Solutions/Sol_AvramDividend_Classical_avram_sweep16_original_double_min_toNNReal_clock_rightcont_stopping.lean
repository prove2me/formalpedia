-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:29:06.895958+00:00
-- url     : https://prove2.me/submissions/be86d35a-fb35-42d1-91c9-64ee905a1542

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_rightcont_stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-! The original finite NNReal clock is an exact physical stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        (S k ω)).toNNReal : WithTop ℝ≥0)) := by
  intro k
  have hStop :=
    avram_sweep16_original_double_min_clock_rightcont_stopping
      X x C D hD n S hSstop k
  have hEq :
      (fun ω => ((min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        (S k ω)).toNNReal : WithTop ℝ≥0)) =
      (fun ω => min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) := by
    funext ω
    exact (avram_sweep16_original_double_min_clock_literal_extended_bounds
      X x D n S k ω).1
  rw [hEq]
  exact hStop
