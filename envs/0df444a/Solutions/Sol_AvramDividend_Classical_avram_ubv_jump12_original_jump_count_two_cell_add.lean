-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_jump_count_two_cell_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:50:26.343038+00:00
-- url     : https://prove2.me/submissions/dc461b5d-d6fa-46df-8989-421b998c91b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc a c ×ˢ B) =
      J (Ioc a b ×ˢ B) + J (Ioc b c ×ˢ B) := by
  classical
  let J : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
     (fun u : ℝ≥0 => (u,
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hUnion :
      (Ioc a b ×ˢ B) ∪ (Ioc b c ×ˢ B) = Ioc a c ×ˢ B := by
    calc
      (Ioc a b ×ˢ B) ∪ (Ioc b c ×ˢ B)
          = (Ioc a b ∪ Ioc b c) ×ˢ B := Set.union_prod.symm
      _ = Ioc a c ×ˢ B := by
        rw [Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  have hDisjoint :
      Disjoint (Ioc a b ×ˢ B) (Ioc b c ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact (not_lt_of_ge hp.1.2) hp'.1.1
  have hMeas : MeasurableSet (Ioc b c ×ˢ B) :=
    measurableSet_Ioc.prod hB
  change J (Ioc a c ×ˢ B) =
    J (Ioc a b ×ˢ B) + J (Ioc b c ×ˢ B)
  rw [← hUnion]
  exact measure_union hDisjoint hMeas
