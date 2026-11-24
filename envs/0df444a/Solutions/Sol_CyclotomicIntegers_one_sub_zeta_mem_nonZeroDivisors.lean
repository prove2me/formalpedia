-- Prove2me | solution 1 for CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:22.483994+00:00
-- url     : https://prove2.me/submissions/fafd405b-e4f6-4d5e-b232-f60311d7303f

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Theorems.Thm_CyclotomicIntegers_prime_one_sub_zeta

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers
namespace CyclotomicIntegers
theorem _root_.solution :
    1 - zeta p ∈ nonZeroDivisors (CyclotomicIntegers p) := by
  simpa only [mem_nonZeroDivisors_iff_ne_zero] using (prime_one_sub_zeta p).1
end CyclotomicIntegers
