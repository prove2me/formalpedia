-- Prove2me | solution 1 for FLT_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:59.320964+00:00
-- url     : https://prove2.me/submissions/123be965-ad11-4bf4-a7a7-b0c0d0d31f6d

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
public import Definitions.Def_FltRegular_SmallNumbers_SmallNumbers
public import Theorems.Thm_FltRegular_fermatLastTheoremFive
public import Theorems.Thm_FltRegular_fermatLastTheoremSeven


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {n : ℕ} (hn : n ∈ Finset.Icc 3 10) : FermatLastTheoremFor n := by
  fin_cases hn
  · exact fermatLastTheoremThree
  · exact fermatLastTheoremFour
  · exact fermatLastTheoremFive
  · exact fermatLastTheoremThree.mono (show 3 ∣ 6 by decide)
  · exact fermatLastTheoremSeven
  · exact fermatLastTheoremFour.mono (show 4 ∣ 8 by decide)
  · exact fermatLastTheoremThree.mono (show 3 ∣ 9 by decide)
  · exact fermatLastTheoremFive.mono (show 5 ∣ 10 by decide)
