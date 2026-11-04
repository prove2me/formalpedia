-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_time_split_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:50:25.178908+00:00
-- url     : https://prove2.me/submissions/1ad3e6d9-e094-4184-81c6-b5c423df16d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Additivity of the true Lévy marked jump measure across adjacent
future time intervals; no Poisson copy or ν-rate is introduced. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) (ω : Ω) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s u ×ˢ B) =
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ B) +
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc t u ×ˢ B) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))
  have hUnion : Ioc s u = Ioc s t ∪ Ioc t u := by
    ext v
    constructor
    · intro hv
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨hv.1, hvt⟩
      · exact Or.inr ⟨lt_of_not_ge hvt, hv.2⟩
    · rintro (hv | hv)
      · exact ⟨hv.1, le_trans hv.2 htu⟩
      · exact ⟨lt_of_le_of_lt hst hv.1, hv.2⟩
  have hRect : Ioc s u ×ˢ B =
      (Ioc s t ×ˢ B) ∪ (Ioc t u ×ˢ B) := by
    ext z
    rw [Set.mem_prod, hUnion]
    simp only [Set.mem_union, Set.mem_prod]
    tauto
  have hDisj : Disjoint (Ioc s t ×ˢ B) (Ioc t u ×ˢ B) := by
    refine Set.disjoint_left.mpr ?_
    intro z hz1 hz2
    exact (not_lt_of_ge hz1.1.2) hz2.1.1
  change μ (Ioc s u ×ˢ B) =
    μ (Ioc s t ×ˢ B) + μ (Ioc t u ×ˢ B)
  rw [hRect]
  exact measure_union hDisj (measurableSet_Ioc.prod hB)
