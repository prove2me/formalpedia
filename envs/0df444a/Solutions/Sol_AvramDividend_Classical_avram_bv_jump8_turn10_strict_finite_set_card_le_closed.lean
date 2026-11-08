-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_strict_finite_set_card_le_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:00:18.493433+00:00
-- url     : https://prove2.me/submissions/007d478e-6ecc-4061-b730-0e442e33accd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A true strict negative original jump belongs to the closed band used by
the existing quadratic collision estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    (avram_redux19_original_strict_negative_marked_times_finite
      X ω T k).toFinset.card ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((k : ℝ) + 1))}.ncard := by
  have hcount :
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
          -(1 / ((k : ℝ) + 1))}.ncard ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((k : ℝ) + 1))}.ncard := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, hu.2.1, le_of_lt hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite
        X ω T k
  have hstrictFinite := avram_redux19_original_strict_negative_marked_times_finite X ω T k
  change hstrictFinite.toFinset.card ≤ _
  rw [← Set.ncard_eq_toFinset_card _ hstrictFinite]
  exact hcount
