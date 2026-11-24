-- Prove2me | solution 1 for FltRegular.fermatLastTheoremSeven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:05.287169+00:00
-- url     : https://prove2.me/submissions/9aaa71e8-647f-49e8-9df1-aa0fbb3a6a55

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
public import Theorems.Thm_isRegularPrime_seven
public import Theorems.Thm_FltRegular_flt_regular


set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension
theorem _root_.solution : FermatLastTheoremFor 7 :=
  @flt_regular 7 ⟨Nat.prime_seven⟩ isRegularPrime_seven (by lia)
