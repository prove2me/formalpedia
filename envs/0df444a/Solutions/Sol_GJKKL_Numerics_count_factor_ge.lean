-- Prove2me | solution 1 for GJKKL.Numerics.count_factor_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:07.089922+00:00
-- url     : https://prove2.me/submissions/6975ec6c-a811-4ae0-9acc-84fcfc0d03b4

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
public import Theorems.Thm_GJKKL_Numerics_exp_neg_le_prod_one_sub
public import Theorems.Thm_GJKKL_Numerics_pow_div_mul_factorial_le_prod

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution (a : ℝ) (ha : 0 < a) (m j : ℕ) (hm : (m : ℝ) ≤ a) :
    exp (-((j : ℝ) * m)) * (a / m) ^ m ≤
      a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ (j + 1) / m.factorial := by
  set P := ∏ i ∈ range m, (1 - (i : ℝ) / a) with hP
  have hP0 : exp (-(m : ℝ)) ≤ P := exp_neg_le_prod_one_sub a ha m hm
  have haP : a ^ m * P = ∏ i ∈ range m, (a - i) := by
    rw [hP, show a ^ m = ∏ _i ∈ range m, a by rw [prod_const, card_range], ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    field_simp
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hbin : (a / m) ^ m ≤ (∏ i ∈ range m, (a - i)) / m.factorial := by
    rw [le_div_iff₀ hfac]
    exact pow_div_mul_factorial_le_prod a m hm
  have hpow : exp (-((j : ℝ) * m)) ≤ P ^ j := by
    rw [show -((j : ℝ) * m) = j * (-(m : ℝ)) by ring, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le hP0 j
  have hbin0 : 0 ≤ (a / m) ^ m := pow_nonneg (div_nonneg ha.le (Nat.cast_nonneg m)) m
  calc exp (-((j : ℝ) * m)) * (a / m) ^ m
      ≤ P ^ j * ((∏ i ∈ range m, (a - i)) / m.factorial) :=
        mul_le_mul hpow hbin hbin0 (pow_nonneg ((exp_pos _).le.trans hP0) j)
    _ = a ^ m * P ^ (j + 1) / m.factorial := by
        rw [← haP, pow_succ]; ring
end GJKKL.Numerics
