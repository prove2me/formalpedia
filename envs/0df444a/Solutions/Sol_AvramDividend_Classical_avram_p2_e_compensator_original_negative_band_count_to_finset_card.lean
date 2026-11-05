-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_count_to_finset_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:47:52.040547+00:00
-- url     : https://prove2.me/submissions/c1486d9c-9e1e-4f2f-aa51-d35405f7b2b1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Explicit original jump count follows from the established source factorial pair identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ((avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset.card : ℝ≥0∞) := by
  simpa only [] using
    (avram_p4_f_assembly_original_negative_band_factorial_pair_identity
      X ω T n).1
