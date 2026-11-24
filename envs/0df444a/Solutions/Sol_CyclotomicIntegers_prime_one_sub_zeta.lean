-- Prove2me | solution 1 for CyclotomicIntegers.prime_one_sub_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:11.076814+00:00
-- url     : https://prove2.me/submissions/77f5ac98-0f37-4bfb-8569-cf265ea03b00

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Theorems.Thm_CyclotomicIntegers_equiv_zeta

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers
namespace CyclotomicIntegers
theorem _root_.solution :
    Prime (1 - zeta p) := by
  rw [← prime_units_mul (u := -1), Units.val_neg, Units.val_one, neg_mul, one_mul, neg_sub]
  apply (MulEquiv.prime_iff (equiv p)).1
  simp only [(equiv p).map_sub, (equiv p).map_one, equiv_zeta]
  exact (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).zeta_sub_one_prime'
end CyclotomicIntegers
