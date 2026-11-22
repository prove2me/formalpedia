-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:08:50.754985+00:00
-- url     : https://prove2.me/submissions/fa6ee6c4-12ff-4b08-86a7-abebe69073dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ Ioc a c) μ) :
    (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a c, p.2 ∂μ) =
      (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a b, p.2 ∂μ) +
      (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc b c, p.2 ∂μ) := by
  classical
  let U : Set ℝ≥0 := Ioc 0 T
  let A : Set (ℝ≥0 × ℝ) := U ×ˢ Ioc a b
  let B : Set (ℝ≥0 × ℝ) := U ×ˢ Ioc b c
  let C : Set (ℝ≥0 × ℝ) := U ×ˢ Ioc a c
  have hUnion : A ∪ B = C := by
    dsimp [A, B, C]
    rw [← Set.prod_union, Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  have hDisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.2.2) hq.2.1
  have hIA : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) A μ := by
    apply hInt.mono_set
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, le_trans hp.2.2 hbc⟩⟩
  have hIB : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) B μ := by
    apply hInt.mono_set
    intro p hp
    exact ⟨hp.1, ⟨lt_of_le_of_lt hab hp.2.1, hp.2.2⟩⟩
  have hAdd := setIntegral_union hDisj
    (measurableSet_Ioc.prod measurableSet_Ioc) hIA hIB
  rw [hUnion] at hAdd
  exact hAdd
