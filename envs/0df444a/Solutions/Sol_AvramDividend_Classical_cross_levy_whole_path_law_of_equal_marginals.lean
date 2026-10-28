-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_whole_path_law_of_equal_marginals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:28:53.345218+00:00
-- url     : https://prove2.me/submissions/6649ee5a-82eb-4b0e-9569-7f2fad297963

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
import Theorems.Thm_AvramDividend_Classical_cross_sample_finite_coord_law_of_grid_vector_law
import Theorems.Thm_AvramDividend_Classical_finite_time_set_has_monotone_zero_started_grid
import Theorems.Thm_AvramDividend_Classical_cross_levy_zeroBasedGrid_law_of_marginals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by
  letI : IsProbabilityMeasure P₁ := X.isProbability
  have hX : Measurable (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) :=
    measurable_pi_iff.mpr (fun u => X.adapted.measurable)
  have hY : Measurable (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) :=
    measurable_pi_iff.mpr (fun u => Y.adapted.measurable)
  apply cross_sample_path_law_eq_of_all_finite_vector_laws
    P₁ P₂ (fun ω u => X.X u ω) (fun ω u => Y.X u ω) hX hY
    (by simp)
  intro J
  obtain ⟨t, ht, ht0, n, henum⟩ :=
    finite_time_set_has_monotone_zero_started_grid J
  have hGrid :=
    cross_levy_zeroBasedGrid_law_of_marginals
      X Y hMarginal t ht ht0 n
  exact cross_sample_finite_coord_law_of_grid_vector_law
    P₁ P₂ (fun ω u => X.X u ω) (fun ω u => Y.X u ω)
    (fun u => X.adapted.measurable) (fun u => Y.adapted.measurable)
    J t n henum hGrid
