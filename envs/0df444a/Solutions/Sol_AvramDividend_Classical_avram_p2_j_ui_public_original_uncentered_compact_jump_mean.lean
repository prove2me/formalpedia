-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_uncentered_compact_jump_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T01:01:44.007048+00:00
-- url     : https://prove2.me/submissions/b113582f-0419-4e73-b5bc-3890d25520c5

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_centered_uncentered_jump_delta

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The public original compact-test mean theorem has its genuine uncentred jump form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∫ ω, J ω ∂P) =
        (T : ℝ) * (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
  obtain ⟨J, hJInt, hRep, hMean⟩ :=
    avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
      P X f hf hc hneg a ε hε hflower hfupper hXm T hT
  refine ⟨J, hJInt, ?_, hMean⟩
  intro ω
  obtain ⟨F, hF, hJ⟩ := hRep ω
  refine ⟨F, ?_, ?_⟩
  · intro u
    by_cases hu : 0 < u
    · simpa only [avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
        X ω u hu] using hF u
    · constructor
      · intro huF
        exact False.elim (hu ((hF u).mp huF).1)
      · intro h
        exact False.elim (hu h.1)
  · calc
      J ω = ∑ u ∈ F, f ((X.X u ω - X.X 0 ω) -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) u) := hJ
      _ = ∑ u ∈ F, f (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
          apply Finset.sum_congr rfl
          intro u huF
          have hu : 0 < u := ((hF u).mp huF).1
          rw [avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
            X ω u hu]
