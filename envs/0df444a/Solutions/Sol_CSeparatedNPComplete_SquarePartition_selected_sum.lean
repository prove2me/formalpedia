-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.selected_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:06.061854+00:00
-- url     : https://prove2.me/submissions/da9b6300-47f2-406c-af91-6cdfef5add80

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (selector N b) (values N a K) = (leftSum N N a K b : ℝ) := by
  simp only [dot, Fin.sum_univ_add, selector, values, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  simp only [leftSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp
end CSeparatedNPComplete.SquarePartition
