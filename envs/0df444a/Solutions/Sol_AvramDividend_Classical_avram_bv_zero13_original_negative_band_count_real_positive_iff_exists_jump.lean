-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:38:00.57541+00:00
-- url     : https://prove2.me/submissions/16b08d09-617b-433c-b8b8-82d24dbd7f6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive real count of actual cutoff jumps detects a physical source jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    0 < (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal ↔
      ∃ u : ℝ≥0, 0 < u ∧ u ≤ T ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1)) := by
  classical
  let S : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ u ≤ T ∧
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}
  have hfinite : S.Finite := by
    simpa only [S] using
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n)
  have hcard :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        (S.ncard : ℝ≥0∞) := by
    simpa only [S] using
      (avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
        X ω T n)
  change 0 < (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal ↔
      S.Nonempty
  rw [hcard, ENNReal.toReal_natCast]
  simpa only [Nat.cast_pos] using (Set.ncard_pos hfinite)
