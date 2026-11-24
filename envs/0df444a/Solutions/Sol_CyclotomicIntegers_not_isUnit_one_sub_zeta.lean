-- Prove2me | solution 1 for CyclotomicIntegers.not_isUnit_one_sub_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:38.270516+00:00
-- url     : https://prove2.me/submissions/1c3ec6a9-5634-4471-9209-1dd67dabf795

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
    ¬ IsUnit (1 - zeta p) := (prime_one_sub_zeta p).irreducible.1
end CyclotomicIntegers
