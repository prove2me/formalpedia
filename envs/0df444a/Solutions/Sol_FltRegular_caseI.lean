-- Prove2me | solution 1 for FltRegular.caseI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:57.191492+00:00
-- url     : https://prove2.me/submissions/33c52cd1-2292-4e34-8719-74527d147198

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Theorems.Thm_FltRegular_CaseI_may_assume
public import Theorems.Thm_FltRegular_caseI_easier

set_option autoImplicit false
@[expose] public section
public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
open FltRegular
variable {p : ℕ}
local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K
variable [hpri : Fact p.Prime]
namespace FltRegular
theorem _root_.solution {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p)
    (caseI : ¬↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  FltRegular.CaseI.may_assume
    (fun _ _ _ _ _ hreg hp5 hunit hxy hI h ↦ caseI_easier hreg hp5 hunit hxy hI h) hreg (by assumption)
end FltRegular
