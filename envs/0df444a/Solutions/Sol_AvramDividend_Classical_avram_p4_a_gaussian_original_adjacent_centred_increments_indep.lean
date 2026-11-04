-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increments_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:42:12.574729+00:00
-- url     : https://prove2.me/submissions/0984831c-2b7b-486c-a118-5798576f895c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Adjacent drift-centred increments of the original source are independent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance) P := by
  have ht : Measurable[𝓕 t] (Y.X t) := Y.adapted t
  have hs : Measurable[𝓕 t] (Y.X s) :=
    (Y.adapted s).mono (𝓕.mono hst) le_rfl
  have hEarlier : Measurable[𝓕 t]
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) :=
    (ht.sub hs).sub measurable_const
  have hLE :
      MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance ≤ 𝓕 t := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
    exact hEarlier hB
  exact indep_of_indep_of_le_right
    (avram_p4_a_gaussian_original_centred_increment_indep_past Y t u htu) hLE
