-- Prove2me | solution 1 for CyclotomicIntegers.one_sub_zeta_dvd_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:51.293594+00:00
-- url     : https://prove2.me/submissions/59a972f4-cfcc-4fc2-992c-400b269da2a2

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
theorem _root_.solution (n : ℤ) : 1 - zeta p ∣ n ↔ ↑p ∣ n := by
  rw [← map_dvd_iff (equiv p), map_sub, map_one, equiv_zeta, map_intCast,
    ← neg_dvd, neg_sub]
  exact IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p
    (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ))
end CyclotomicIntegers
