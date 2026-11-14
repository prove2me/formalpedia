-- Prove2me | solution 1 for AvramDividend.Classical.avram_b83_original_finite_negative_activity_small_mark_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T14:22:23.881704+00:00
-- url     : https://prove2.me/submissions/7f5bc43f-a2c0-439a-9b1a-3ea179901d72

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite physical negative source jump activity implies finite signed small negative-mark first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) 0) X.ν := by
  have hSub : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hz.2
  have hMass : X.ν (Ioo (-1 : ℝ) 0) < ⊤ := by
    have hNe : X.ν (Ioo (-1 : ℝ) 0) ≠ ⊤ :=
      ne_top_of_le_ne_top hFinite (measure_mono hSub)
    exact lt_top_iff_ne_top.mpr hNe
  apply IntegrableOn.of_bound hMass
    (measurable_id.aestronglyMeasurable) (1 : ℝ)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rw [Real.norm_eq_abs]
  change |z| ≤ (1 : ℝ)
  have hz0 : z ≤ 0 := le_of_lt hz.2
  rw [abs_of_nonpos hz0]
  linarith [hz.1]
