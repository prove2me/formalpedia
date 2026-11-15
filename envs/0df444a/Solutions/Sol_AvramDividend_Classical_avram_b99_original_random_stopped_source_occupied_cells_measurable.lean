-- Prove2me | solution 1 for AvramDividend.Classical.avram_b99_original_random_stopped_source_occupied_cells_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:29:11.948554+00:00
-- url     : https://prove2.me/submissions/18b6f584-42d4-4fbf-8e36-2a429103c5d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original negative-band occupied-cell count is measurable for genuine random source grid clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (S : Finset ℕ)
    (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i ∈ S, Measurable (s i))
    (ht : ∀ i ∈ S, Measurable (t i)) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ S,
        if ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i ω) (t i ω) ×ˢ
              Iic (-(1 / ((cut : ℝ) + 1)))) ≠ 0 then
          (1 : ℝ≥0∞) else 0) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  have hm :=
    avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
      X cut (s i) (t i) (hs i hi) (ht i hi)
  have hset : MeasurableSet {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i ω) (t i ω) ×ˢ
              Iic (-(1 / ((cut : ℝ) + 1)))) ≠ 0} := by
    exact (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hm
  exact Measurable.ite hset measurable_const measurable_const
