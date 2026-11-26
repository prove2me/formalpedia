-- Prove2me | solution 1 for Erdos266.summable_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:57.258091+00:00
-- url     : https://prove2.me/submissions/a56aaddf-0079-4c67-831a-6058dd64cd78

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}
namespace Erdos266
theorem _root_.solution (ha : StrictMono a)
    (hsum : Summable fun n => ((a n : ℝ))⁻¹) (c : ℝ) :
    Summable fun n => ((a n : ℝ) + c)⁻¹ := by
  set N := ⌈2 * |c| + 1⌉₊ with hN
  have hbig : ∀ n : ℕ, N ≤ n → 2 * |c| + 1 ≤ (a n : ℝ) := by
    intro n hn
    calc 2 * |c| + 1 ≤ (N : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (a n : ℝ) := by exact_mod_cast ha.le_apply
  refine (summable_nat_add_iff N).mp ?_
  change Summable fun n => ((a (n + N) : ℝ) + c)⁻¹
  have hhalf : ∀ n : ℕ, (a (n + N) : ℝ) / 2 ≤ (a (n + N) : ℝ) + c := by
    intro n
    have h1 := hbig (n + N) (Nat.le_add_left N n)
    have h2 : -|c| ≤ c := neg_abs_le c
    nlinarith [abs_nonneg c]
  have hpos : ∀ n : ℕ, 0 < (a (n + N) : ℝ) := by
    intro n
    have h1 := hbig (n + N) (Nat.le_add_left N n)
    nlinarith [abs_nonneg c]
  refine Summable.of_nonneg_of_le
    (fun n => le_of_lt (inv_pos.mpr (lt_of_lt_of_le (half_pos (hpos n)) (hhalf n))))
    (fun n => ?_) ((summable_nat_add_iff N).mpr (hsum.mul_left 2))
  calc ((a (n + N) : ℝ) + c)⁻¹
      ≤ ((a (n + N) : ℝ) / 2)⁻¹ := inv_anti₀ (half_pos (hpos n)) (hhalf n)
  _ = 2 * ((a (n + N) : ℝ))⁻¹ := by
        rw [inv_div, div_eq_mul_inv]
end Erdos266
