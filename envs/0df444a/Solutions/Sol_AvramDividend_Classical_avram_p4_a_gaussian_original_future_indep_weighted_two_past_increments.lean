-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_weighted_two_past_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:35:29.299607+00:00
-- url     : https://prove2.me/submissions/5209dbd2-45c8-480e-beff-d00c86901bf6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- A future source increment is independent of the weighted sum of two earlier increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (α β : ℝ) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X v ω - Y.X u ω) - ((v - u : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => α * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
          β * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c))
        inferInstance) P := by
  have hu : Measurable[𝓕 u] (Y.X u) := Y.adapted u
  have ht : Measurable[𝓕 u] (Y.X t) :=
    (Y.adapted t).mono (𝓕.mono htu) le_rfl
  have hs : Measurable[𝓕 u] (Y.X s) :=
    (Y.adapted s).mono (𝓕.mono (hst.trans htu)) le_rfl
  have hMid : Measurable[𝓕 u]
      (fun ω => (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) :=
    (hu.sub ht).sub measurable_const
  have hEarly : Measurable[𝓕 u]
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) :=
    (ht.sub hs).sub measurable_const
  have hPast : Measurable[𝓕 u]
      (fun ω => α * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
        β * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) :=
    (measurable_const.mul hMid).add (measurable_const.mul hEarly)
  have hLE :
      MeasurableSpace.comap
        (fun ω => α * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
          β * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c))
        inferInstance ≤ 𝓕 u := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
    exact hPast hB
  exact indep_of_indep_of_le_right
    (avram_p4_a_gaussian_original_centred_increment_indep_past Y u v huv) hLE
