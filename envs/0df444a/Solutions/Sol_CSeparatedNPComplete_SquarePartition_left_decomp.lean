-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.left_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:14.112491+00:00
-- url     : https://prove2.me/submissions/4a2c1752-cdc4-4308-9704-26677c48e1c6

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_gap

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hm : m ≤ N) (hbound : ∀ i, i < m → a i ≤ K ^ (2 * i)) :
    leftSum N m a K b = (∑ i : Fin m, minus N a K i) +
      4 * K ^ (2 * N) * chooseSum m a b := by
  unfold leftSum chooseSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hg := gap N a K i (by omega) (hbound i i.isLt)
  cases b i <;> simp [hg]
end CSeparatedNPComplete.SquarePartition
