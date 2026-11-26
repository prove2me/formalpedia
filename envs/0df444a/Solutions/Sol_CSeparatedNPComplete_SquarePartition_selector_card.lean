-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.selector_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:04.338309+00:00
-- url     : https://prove2.me/submissions/0a563ad5-ff03-4c3c-bd13-1d033782cd6d

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (b : ℕ → Bool) : dot (selector N b) 1 = (N : ℝ) := by
  simp only [dot, Fin.sum_univ_add, selector, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one]
  rw [← Finset.sum_add_distrib]
  have h (i : Fin N) : (if b i then (1 : ℝ) else 0) + (if b i then 0 else 1) = 1 := by
    cases b i <;> norm_num
  simp_rw [h]
  simp
end CSeparatedNPComplete.SquarePartition
