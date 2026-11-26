-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.base_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:26.66984+00:00
-- url     : https://prove2.me/submissions/fb3c4b84-394f-4a3d-a750-764469c43528

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (M : ℕ) (ha : ∀ i, a i ≤ M) :
    base a ≤ 2 + n + 2 * n * M + n * M ^ 2 := by
  have hs : ∑ i, a i ≤ n * M := by
    calc
      _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => ha i
      _ = _ := by simp
  have hq : ∑ i, (a i) ^ 2 ≤ n * M ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, M ^ 2 := Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (ha i) 2
      _ = _ := by simp
  unfold base
  nlinarith
end CSeparatedNPComplete.SquareReduction
