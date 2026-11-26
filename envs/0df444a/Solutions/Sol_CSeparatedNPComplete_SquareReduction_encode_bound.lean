-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.encode_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:23.9278+00:00
-- url     : https://prove2.me/submissions/c959f570-ecd3-45fa-a537-b7633035ed58

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_lt_upper

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (i : Fin (n + n)) :
    encode a i ≤ base a ^ (4 * (n + 1)) := by
  have hK := base_ge_two a
  have hp (j : Fin n) : (upper a j + lower a j) ^ 2 ≤ base a ^ (4 * (n + 1)) := by
    have hr : upper a j + lower a j ≤ base a ^ (2 * (n + 1)) := by
      calc
        _ ≤ 2 * upper a j := by have := lower_lt_upper a j; omega
        _ ≤ base a * upper a j := Nat.mul_le_mul_right _ hK
        _ = base a ^ (n + j.val + 2) := by simp [upper, pow_succ, mul_comm]
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      _ ≤ (base a ^ (2 * (n + 1))) ^ 2 := Nat.pow_le_pow_left hr 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [encode, Fin.append_left] using hp j
  · intro j
    simp only [encode, Fin.append_right]
    exact (Nat.pow_le_pow_left (show upper a j - lower a j ≤ upper a j + lower a j by omega) 2).trans (hp j)
end CSeparatedNPComplete.SquareReduction
