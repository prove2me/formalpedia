-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:57:29.195311+00:00
-- url     : https://prove2.me/submissions/8816ce64-924b-4cdd-bbb7-198a904e321b

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_finite_negative_small_mark_square_integrable_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_negative_cutoff_retained_omitted_partition_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The original Lévy quadratic mark mass partitions exactly at a cutoff. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤) (n : ℕ) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂ν) =
      (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ^ 2 ∂ν) +
      (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂ν) := by
  let A : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let B : Set ℝ := Ioo (-(1 / ((n : ℝ) + 1))) 0
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  have hUnion : A ∪ B = S :=
    avram_a21_negative_cutoff_retained_omitted_partition_20261113 n
  have hDisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact (not_lt_of_ge hzA.2) hzB.1
  have hInt := avram_a21_original_finite_negative_small_mark_square_integrable_20261113
    ν hFinite
  have hA : A ⊆ S := by
    rw [← hUnion]
    exact subset_union_left
  have hB : B ⊆ S := by
    rw [← hUnion]
    exact subset_union_right
  have hIntA : IntegrableOn (fun z : ℝ => z ^ 2) A ν :=
    hInt.mono_set hA
  have hIntB : IntegrableOn (fun z : ℝ => z ^ 2) B ν :=
    hInt.mono_set hB
  change (∫ z in S, z ^ 2 ∂ν) =
    (∫ z in A, z ^ 2 ∂ν) + (∫ z in B, z ^ 2 ∂ν)
  rw [← hUnion]
  exact setIntegral_union hDisj measurableSet_Ioo hIntA hIntB
