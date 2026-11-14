-- Prove2me | solution 1 for AvramDividend.Classical.avram_b166_original_random_grid_negative_cutoff_occupied_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:58:11.314213+00:00
-- url     : https://prove2.me/submissions/9caf0d59-5c29-4302-a51a-914a5e0080a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (S : Finset ℕ)
    (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : Ω → ℕ → ℝ≥0∞ := fun ω i =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => N ω i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro N J
  classical
  have hN (i : ℕ) : Measurable (fun ω => N ω i) := by
    exact avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
      X cut (s i) (t i) (hs i) (ht i)
  have hSum : Measurable (fun ω =>
      ∑ i ∈ S, if N ω i ≠ 0 then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    have hA : MeasurableSet {ω : Ω | N ω i ≠ 0} :=
      (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage (hN i)
    exact Measurable.ite hA measurable_const measurable_const
  have hCard (ω : Ω) :
      (∑ i ∈ S, if N ω i ≠ 0 then (1 : ℝ) else 0) =
        ((J ω).card : ℝ) := by
    simp [J, Finset.sum_ite, Finset.sum_const]
  convert hSum using 1
  funext ω
  exact (hCard ω).symm
