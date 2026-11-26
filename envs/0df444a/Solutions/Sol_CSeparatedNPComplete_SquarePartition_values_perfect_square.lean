-- Prove2me | solution 1 for CSeparatedNPComplete.SquarePartition.values_perfect_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:49:20.348809+00:00
-- url     : https://prove2.me/submissions/a7d9b0ab-2517-42f0-a265-fd5833708d40

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition
namespace CSeparatedNPComplete.SquarePartition
theorem _root_.solution (N : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    perf_square_vec (values N a K) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine ⟨K ^ (N + j.val) + a j.val * K ^ (N - j.val), ?_⟩
    simp only [values, Fin.append_left]
    simp [plus, pow_two]
  · intro j
    refine ⟨K ^ (N + j.val) - a j.val * K ^ (N - j.val), ?_⟩
    simp only [values, Fin.append_right]
    simp [minus, pow_two]
end CSeparatedNPComplete.SquarePartition
