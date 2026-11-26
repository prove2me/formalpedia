-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.lower_lt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:10.89613+00:00
-- url     : https://prove2.me/submissions/df789913-1f13-4326-bb70-68778c1fec12

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_weight_lt_base

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : lower a i < upper a i := by
  have hK := base_ge_two a
  have ha : a i < base a ^ (2 * (i.val + 1)) :=
    lt_of_lt_of_le (weight_lt_base a i)
      (le_self_pow₀ (by omega : 1 ≤ base a) (by omega))
  calc
    lower a i < base a ^ (2 * (i.val + 1)) * base a ^ (n - (i.val + 1)) :=
      Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ = upper a i := by unfold upper; rw [← pow_add]; congr 1; omega
end CSeparatedNPComplete.SquareReduction
