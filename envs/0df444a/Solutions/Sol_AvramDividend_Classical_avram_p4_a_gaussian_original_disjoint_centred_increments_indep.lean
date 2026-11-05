-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_disjoint_centred_increments_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:29:55.326989+00:00
-- url     : https://prove2.me/submissions/46290e66-2011-43e1-bed7-0cea8619216d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Drift-centred increments over disjoint ordered original-process intervals are independent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X v ω - Y.X u ω) - ((v - u : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance) P := by
  have ht : Measurable[𝓕 u] (Y.X t) :=
    (Y.adapted t).mono (𝓕.mono htu) le_rfl
  have hs : Measurable[𝓕 u] (Y.X s) :=
    (Y.adapted s).mono (𝓕.mono (hst.trans htu)) le_rfl
  have hEarlier : Measurable[𝓕 u]
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) :=
    (ht.sub hs).sub measurable_const
  have hLE :
      MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance ≤ 𝓕 u := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
    exact hEarlier hB
  exact indep_of_indep_of_le_right
    (avram_p4_a_gaussian_original_centred_increment_indep_past Y u v huv) hLE
