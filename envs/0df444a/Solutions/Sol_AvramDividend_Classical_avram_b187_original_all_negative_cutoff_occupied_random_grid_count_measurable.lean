-- Prove2me | solution 1 for AvramDividend.Classical.avram_b187_original_all_negative_cutoff_occupied_random_grid_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:45:05.880699+00:00
-- url     : https://prove2.me/submissions/a16239e6-a2f1-417c-9363-2b28e01d9891

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
attribute [local instance] Classical.propDecidable

/-- The number of original random physical grid cells occupied by at least one reciprocal negative-cutoff marked Poisson source is a measurable real random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : Ω → ℕ → ℕ → ℝ≥0∞ := fun ω n i =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ n : ℕ, N ω n i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro N J
  classical
  let A : ℕ → ℕ → Ω → Prop := fun n i ω => N ω n i ≠ 0
  have hA : ∀ n i, MeasurableSet {ω : Ω | A n i ω} := by
    intro n i
    have hN :=
      avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
        X n (s i) (t i) (hs i) (ht i)
    exact (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hN
  have h :=
    avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
      S A hA
  change Measurable (fun ω =>
    ((S.filter (fun i => ∃ n : ℕ, A n i ω)).card : ℝ)) at h
  simpa only [J, A] using h
