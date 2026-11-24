-- Prove2me | solution 1 for CyclotomicIntegers.one_sub_zeta_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:18.642806+00:00
-- url     : https://prove2.me/submissions/17ecef70-78df-49ee-acf1-8137a214f051

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Theorems.Thm_CyclotomicIntegers_one_sub_zeta_dvd_int_iff

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers
namespace CyclotomicIntegers
theorem _root_.solution : 1 - zeta p ∣ p :=
  (one_sub_zeta_dvd_int_iff _ _).2 dvd_rfl
end CyclotomicIntegers
