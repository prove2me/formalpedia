-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.lower_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:44.79543+00:00
-- url     : https://prove2.me/submissions/72d9a32f-7a5b-4c2c-88ab-3f47415d67aa

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (lower a i : ℝ) ^ 2 ≤ (a i : ℝ) ^ 2 * (base a : ℝ) ^ (2 * n) := by
  simp only [lower, Nat.cast_mul, Nat.cast_pow, mul_pow, ← pow_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply pow_le_pow_right₀
  · exact_mod_cast (base_ge_two a).trans' (by decide : 1 ≤ 2)
  · omega
end CSeparatedNPComplete.SquareReduction
