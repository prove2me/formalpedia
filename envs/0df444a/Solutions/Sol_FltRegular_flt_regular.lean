-- Prove2me | solution 1 for FltRegular.flt_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:26:11.227505+00:00
-- url     : https://prove2.me/submissions/c9161c56-8fba-4452-93b0-879375b356ef

module
public import Mathlib.NumberTheory.FLT.Basic
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Definitions.Def_FltRegular_CaseII_Statement
public import Definitions.Def_FltRegular_FltRegular
public import Theorems.Thm_FltRegular_caseI
public import Theorems.Thm_FltRegular_caseII


set_option autoImplicit false
@[expose] public section
public section
open FltRegular
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  rw [fermatLastTheoremFor_iff_int]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd
  by_cases hcase : ↑p ∣ a * b * c
  · exact caseII hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd hcase
  · exact caseI hreg hcase
