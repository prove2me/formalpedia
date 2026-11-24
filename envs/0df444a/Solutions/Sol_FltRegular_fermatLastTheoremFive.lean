-- Prove2me | solution 1 for FltRegular.fermatLastTheoremFive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:04.865369+00:00
-- url     : https://prove2.me/submissions/6f2b8f57-a246-4305-82e4-05959da0ec1d

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
public import Theorems.Thm_isRegularPrime_five
public import Theorems.Thm_FltRegular_flt_regular


set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension
theorem _root_.solution : FermatLastTheoremFor 5 :=
  @flt_regular 5 ⟨Nat.prime_five⟩ isRegularPrime_five (by lia)
