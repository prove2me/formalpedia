-- Prove2me | solution 1 for CSeparatedNPComplete.square_reduction_positive_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:51.007987+00:00
-- url     : https://prove2.me/submissions/f04534e1-7663-44ce-9636-f7a748bcd7c7

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_values_perfect_square
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_values_perfect_square
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_values_positive


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (n : ℕ) (a : Fin n → ℕ) :
    perf_square_vec (SquareReduction.values a) ∧
      ∀ i, 0 < SquareReduction.values a i :=
  ⟨SquareReduction.values_perfect_square a, SquareReduction.values_positive a⟩
end CSeparatedNPComplete
