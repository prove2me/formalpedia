-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:46:23.506505+00:00
-- url     : https://prove2.me/submissions/35b2b950-c997-4323-9daf-f1be363addda

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_real_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_jump_equals_centered_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- The original intrinsic compact-negative jump sum has its genuine Lévy-rate mean. -/
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
      (∫ ω, J ω ∂P) = (T : ℝ) *
        (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) := by
  have hRate := avram_p2_j_ui_original_compact_negative_test_real_rate
    X g hg hc hneg
  obtain ⟨J, hJInt, hRep, hMean⟩ :=
    avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
      P X T hT g hg hc hneg
      (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) hRate
  refine ⟨J, hJInt, ?_, hMean⟩
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
