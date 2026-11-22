-- Prove2me | solution 1 for GJKKL.Numerics.pow_div_mul_factorial_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:27.276797+00:00
-- url     : https://prove2.me/submissions/1c10ebef-3d0c-4154-b63b-ca8cc5e6cea5

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
public import Theorems.Thm_GJKKL_Numerics_prod_range_sub_eq_factorial

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution (a : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ a) :
    (a / m) ^ m * m.factorial ≤ ∏ i ∈ range m, (a - i) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have ha0 : 0 ≤ a := hm0'.le.trans hm
  rw [← prod_range_sub_eq_factorial,
    show (a / m) ^ m = ∏ _i ∈ range m, (a / m) by rw [prod_const, card_range],
    ← prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
  · have : (i : ℝ) < m := by exact_mod_cast mem_range.mp hi
    exact mul_nonneg (div_nonneg ha0 hm0'.le) (by linarith)
  · have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0']
    nlinarith
end GJKKL.Numerics
