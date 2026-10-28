-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:37:10.46526+00:00
-- url     : https://prove2.me/submissions/304f096c-1eef-404b-ab2d-071e7c918d4c

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_esscher_density_eq_displacement_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_weighted_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p a : ℝ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X z.2.toNNReal z.1 - X.X s z.1 < a} =
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X s z.1 - X.X 0 z.1 < a} := by
  obtain ⟨hL, hR⟩ :=
    avram_ws01e_b_levy_random_horizon_strict_events_measurable
      X (fun t : ℝ => t.toNNReal) measurable_real_toNNReal a
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  refine avram_ws01e_b_joint_weighted_clock_section_probability_transfer
    P (expMeasure p)
    (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))
    hJoint _ _ hL hR ?_
  intro t
  by_cases ht : 0 < t.toNNReal
  · have h := avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
      X t.toNNReal ht θ a
    rw [avram_ws01e_b_canonical_esscher_density_eq_displacement_density
      X θ t.toNNReal] at h
    exact h
  · have hz : t.toNNReal = 0 :=
      le_antisymm (le_of_not_gt ht) zero_le
    have hLeft :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X t.toNNReal ω - X.X s ω < a} =
        {ω : Ω | 0 < a} := by
      ext ω
      constructor
      · rintro ⟨s, hs, h⟩
        have hs0 : s = 0 := le_antisymm (by simpa [hz] using hs) zero_le
        simpa [hz, hs0] using h
      · intro ha
        exact ⟨0, by simp [hz], by simpa [hz] using ha⟩
    have hRight :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X s ω - X.X 0 ω < a} =
        {ω : Ω | 0 < a} := by
      ext ω
      constructor
      · rintro ⟨s, hs, h⟩
        have hs0 : s = 0 := le_antisymm (by simpa [hz] using hs) zero_le
        simpa [hs0] using h
      · intro ha
        exact ⟨0, by simp [hz], by simpa using ha⟩
    change
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t.toNNReal ω -
          (t.toNNReal : ℝ) * X.ψ θ))))
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X t.toNNReal ω - X.X s ω < a} =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t.toNNReal ω -
          (t.toNNReal : ℝ) * X.ψ θ))))
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X s ω - X.X 0 ω < a}
    rw [hLeft, hRight]
