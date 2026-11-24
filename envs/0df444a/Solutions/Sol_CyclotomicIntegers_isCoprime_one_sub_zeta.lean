-- Prove2me | solution 1 for CyclotomicIntegers.isCoprime_one_sub_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:57.7088+00:00
-- url     : https://prove2.me/submissions/fc69d618-17f7-4030-90f7-b72a065bec3b

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Theorems.Thm_CyclotomicIntegers_one_sub_zeta_dvd

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers
namespace CyclotomicIntegers
theorem _root_.solution (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : IsCoprime (1 - zeta p) n :=
  (((Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd.mpr hn).map
    (algebraMap ℤ <| CyclotomicIntegers p)).of_isCoprime_of_dvd_left (one_sub_zeta_dvd p)
end CyclotomicIntegers
