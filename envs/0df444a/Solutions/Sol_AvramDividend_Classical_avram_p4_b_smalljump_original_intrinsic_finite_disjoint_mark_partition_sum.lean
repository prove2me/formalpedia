-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:22:07.245169+00:00
-- url     : https://prove2.me/submissions/c37bcdaa-63b1-4563-9a7d-db04f54be49d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original Lévy intrinsic jump count over a finite pairwise
disjoint collection of Borel mark bands is the sum of its band counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hDisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ i ∈ S, B i)) =
    ∑ i ∈ S,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i) := by
  classical
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change N (Ioc s t ×ˢ (⋃ i ∈ S, B i)) =
    ∑ i ∈ S, N (Ioc s t ×ˢ B i)
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hBsmall (i : ι) (hi : i ∈ S) : MeasurableSet (B i) :=
      hB i (Finset.mem_insert_of_mem hi)
    have hdsmall (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
        (hij : i ≠ j) : Disjoint (B i) (B j) :=
      hDisj i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij
    have hd : Disjoint (B a) (⋃ i ∈ S, B i) := by
      apply Set.disjoint_left.mpr
      intro z hza hzS
      rcases Set.mem_iUnion.mp hzS with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨hiS, hzi⟩
      have hai : a ≠ i := by
        intro h
        subst i
        exact ha hiS
      exact Set.disjoint_left.mp
        (hDisj a (Finset.mem_insert_self a S) i
          (Finset.mem_insert_of_mem hiS) hai) hza hzi
    have hdProd : Disjoint (Ioc s t ×ˢ B a)
        (Ioc s t ×ˢ (⋃ i ∈ S, B i)) := by
      apply Set.disjoint_left.mpr
      rintro ⟨u,z⟩ h₁ h₂
      exact Set.disjoint_left.mp hd h₁.2 h₂.2
    have hmSmall : MeasurableSet (Ioc s t ×ˢ (⋃ i ∈ S, B i)) := by
      apply MeasurableSet.prod measurableSet_Ioc
      have hmS : MeasurableSet
          (⋃ i : {i : ι // i ∈ S}, B i.val) := by
        exact MeasurableSet.iUnion (fun i => hBsmall i.val i.property)
      have heq : (⋃ i : {i : ι // i ∈ S}, B i.val) =
          (⋃ i ∈ S, B i) := by
        ext z
        simp
      exact heq ▸ hmS
    have hu : (Ioc s t ×ˢ (⋃ i ∈ insert a S, B i)) =
        (Ioc s t ×ˢ B a) ∪ (Ioc s t ×ˢ (⋃ i ∈ S, B i)) := by
      ext ⟨u,z⟩
      simp [Finset.mem_insert, and_or_left]
    calc
      N (Ioc s t ×ˢ (⋃ i ∈ insert a S, B i)) =
          N (Ioc s t ×ˢ B a) +
            N (Ioc s t ×ˢ (⋃ i ∈ S, B i)) := by
        rw [hu, measure_union hdProd hmSmall]
      _ = N (Ioc s t ×ˢ B a) +
          ∑ i ∈ S, N (Ioc s t ×ˢ B i) := by rw [ih hBsmall hdsmall]
      _ = ∑ i ∈ insert a S, N (Ioc s t ×ˢ B i) := by
        rw [Finset.sum_insert ha]
