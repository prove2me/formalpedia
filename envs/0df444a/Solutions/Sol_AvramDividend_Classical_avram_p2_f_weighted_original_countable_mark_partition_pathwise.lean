-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_partition_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:16:01.822837+00:00
-- url     : https://prove2.me/submissions/a3d7a3b4-2f8a-4bd5-87b7-9c1b7c9a2919

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Countable disjoint Borel marks partition the genuine original
intrinsic marked-jump count pathwise, with extended sums and no ν-rate. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) =
      ∑' i, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) := by
  intro ω
  have hSet : Ioc s (s + T) ×ˢ (⋃ i, B i) =
      ⋃ i, Ioc s (s + T) ×ˢ B i := by
    ext p
    simp only [Set.mem_prod, Set.mem_iUnion]
    constructor
    · rintro ⟨ht, i, hi⟩
      exact ⟨i, ht, hi⟩
    · rintro ⟨i, ht, hi⟩
      exact ⟨ht, i, hi⟩
  rw [hSet]
  exact MeasureTheory.measure_iUnion
    (fun i j hij => Set.Disjoint.set_prod_right (hDisj hij)
      (Ioc s (s + T)) (Ioc s (s + T)))
    (fun i => measurableSet_Ioc.prod (hB i))
