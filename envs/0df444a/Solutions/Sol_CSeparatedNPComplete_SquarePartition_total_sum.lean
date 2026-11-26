-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.total_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:13.3334+00:00
-- url     : https://prove2.me/submissions/cdd0f67a-295d-4e71-a80f-89ebffe291a0

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (values N a K) 1 = (leftSum N N a K b : ℝ) + (rightSum N N a K b : ℝ) := by
  simp only [dot, Fin.sum_univ_add, values, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one, leftSum, rightSum, Nat.cast_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp [add_comm]
end CSeparatedNPComplete.SquarePartition
