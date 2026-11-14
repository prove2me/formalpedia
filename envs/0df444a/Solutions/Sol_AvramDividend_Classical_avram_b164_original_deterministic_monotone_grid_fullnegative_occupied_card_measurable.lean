-- Prove2me | solution 1 for AvramDividend.Classical.avram_b164_original_deterministic_monotone_grid_fullnegative_occupied_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:58:02.068208+00:00
-- url     : https://prove2.me/submissions/b1795ef9-2927-4abe-81fd-be550acb5ab3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original full-negative-jump occupied-cell cardinal of any finite monotone deterministic physical grid is a measurable real random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    let N : Ω → ℕ → ℝ≥0∞ := fun ω i =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
        (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ))
    let J : Ω → Finset ℕ := fun ω =>
      (Finset.range m).filter (fun i => N ω i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro N J
  classical
  have hEN : Measurable (fun ω => ∑ i ∈ Finset.range m,
      if N ω i ≠ 0 then (1 : ℝ≥0∞) else 0) :=
    avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
      X u hu m
  have hCard (ω : Ω) :
      (∑ i ∈ Finset.range m, if N ω i ≠ 0 then (1 : ℝ≥0∞) else 0) =
        ((J ω).card : ℝ≥0∞) := by
    simp [J, Finset.sum_ite, Finset.sum_const]
  have hReal : Measurable (fun ω =>
      (∑ i ∈ Finset.range m,
        if N ω i ≠ 0 then (1 : ℝ≥0∞) else 0).toReal) :=
    ENNReal.measurable_toReal.comp hEN
  convert hReal using 1
  funext ω
  rw [hCard ω]
  simp
