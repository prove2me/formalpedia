-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.values_perfect_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:51.82787+00:00
-- url     : https://prove2.me/submissions/0700c429-756d-4d2c-a36a-fb00ea035d33

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) : perf_square_vec (values a) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine ⟨upper a j + lower a j, ?_⟩
    simp only [values, Fin.append_left, pow_two, Nat.cast_mul]
  · intro j
    refine ⟨upper a j - lower a j, ?_⟩
    simp only [values, Fin.append_right, pow_two, Nat.cast_mul]
end CSeparatedNPComplete.SquareReduction
