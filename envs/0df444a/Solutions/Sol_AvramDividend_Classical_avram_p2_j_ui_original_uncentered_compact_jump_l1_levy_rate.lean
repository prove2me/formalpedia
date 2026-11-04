-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_jump_l1_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:57:46.628638+00:00
-- url     : https://prove2.me/submissions/7483b9c7-4b88-46f6-b82f-3701ac2a08bc

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_negative_uniform_grid_levy_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_jump_equals_centered_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original uncentred tested jump sums are true L1 limits with the source Lévy mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)) ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - J)
        1 P) atTop (nhds 0) ∧
      (∫ ω, J ω ∂P) = (T : ℝ) *
        (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) := by
  obtain ⟨J, hJInt, hRep, hL1, hGridMean⟩ :=
    avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
      P X T hT g hg hc hneg
  have hGridRate := avram_p2_j_ui_original_negative_uniform_grid_levy_mean
    P X T hT g hg hc hneg
  have hExpect : (∫ ω, J ω ∂P) = (T : ℝ) *
      (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) :=
    tendsto_nhds_unique hGridMean hGridRate
  refine ⟨J, hJInt, ?_, hL1, hExpect⟩
  intro ω
  obtain ⟨F, hF, hJ⟩ := hRep ω
  refine ⟨F, ?_, ?_⟩
  · intro u
    by_cases hu : 0 < u
    · simpa only [avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
        X ω u hu] using hF u
    · constructor
      · intro huF
        exact False.elim (hu ((hF u).mp huF).1)
      · intro h
        exact False.elim (hu h.1)
  · calc
      J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) := hJ
      _ = ∑ u ∈ F, g (X.X u ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) := by
          apply Finset.sum_congr rfl
          intro u huF
          have hu : 0 < u := ((hF u).mp huF).1
          rw [avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
            X ω u hu]
