-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward43_original_finite_negative_mark_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:36:13.670626+00:00
-- url     : https://prove2.me/submissions/2530c603-0a9a-46d6-9466-21499f7b6795

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    (∫⁻ ω, ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
       (Ioc 0 T ×ˢ Ioo (-1 : ℝ) (-η)) ∂P) < ⊤ := by
  have hB : MeasurableSet (Ioo (-1 : ℝ) (-η)) := measurableSet_Ioo
  have hNeg : Ioo (-1 : ℝ) (-η) ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact mem_Iio.mpr (lt_trans hz.2 (neg_neg_of_pos hη))
  have hν : X.ν (Ioo (-1 : ℝ) (-η)) < ⊤ := by
    have ht := avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν X.ν_integrable η hη (le_of_lt hη1)
    exact lt_of_le_of_lt (measure_mono (by
      intro z hz
      exact mem_Iic.mpr (le_of_lt hz.2))) ht
  have heq := avram_ja34_original_all_negative_borel_expected_count_exact
    X T (Ioo (-1 : ℝ) (-η)) hB hNeg
  rw [heq]
  exact ENNReal.mul_lt_top (by simp) hν
