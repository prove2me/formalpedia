-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:21:01.162104+00:00
-- url     : https://prove2.me/submissions/1dd86ce5-ff54-4b14-8c8d-979ef05b9492

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The literal strict cutoff of the canonical marked Laplace theorem has finite jump times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    Set.Finite {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))} := by
  have hClosed :=
    AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
      X ω T k
  apply hClosed.subset
  intro u hu
  exact ⟨hu.1, hu.2.1, le_of_lt hu.2.2⟩
