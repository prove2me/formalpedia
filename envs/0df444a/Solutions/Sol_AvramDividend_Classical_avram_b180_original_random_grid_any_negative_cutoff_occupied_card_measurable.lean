-- Prove2me | solution 1 for AvramDividend.Classical.avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:43.772523+00:00
-- url     : https://prove2.me/submissions/7e6e44e5-755a-45b8-8ad3-b4c178ab1112

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical negative-cutoff occupied-grid cardinal is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun cut i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ cut : ℕ, N cut i ω ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  classical
  intro N J
  have hA (cut i : ℕ) :
      MeasurableSet {ω : Ω | N cut i ω ≠ 0} := by
    have hN : Measurable (fun ω => N cut i ω) := by
      simpa only [N] using
        (avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
          X cut (s i) (t i) (hs i) (ht i))
    exact (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hN
  simpa only [J] using
    (avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
      S (fun cut i ω => N cut i ω ≠ 0) hA)
