-- Prove2me | solution 1 for FltRegular.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:07.543095+00:00
-- url     : https://prove2.me/submissions/0760af10-157a-4ae4-ae1e-b7b20d85ba12

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Theorems.Thm_FltRegular_ab_coprime
public import Theorems.Thm_fltIdeals_coprime


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
theorem _root_.solution {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) {ζ : R} (hζ : ζ ∈ nthRootsFinset p 1) :
    ∃ I, span ({a + ζ * b} : Set R) = I ^ p := by
  classical
  have H₁ := congr_arg (@Int.cast R _) H
  simp only [Int.cast_add, Int.cast_pow] at H₁
  have hζ' := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  rw [hζ'.pow_add_pow_eq_prod_add_mul _ _ <|
    odd_iff.2 <| hpri.1.eq_two_or_odd.resolve_left fun h ↦ by simp [h] at h5p] at H₁
  replace H₁ := congr_arg (fun x ↦ span ({x} : Set R)) H₁
  simp only [← prod_span_singleton, ← span_singleton_pow] at H₁
  refine exists_eq_pow_of_mul_eq_pow_of_coprime (fun η₁ hη₁ η₂ hη₂ hη ↦ ?_) H₁ ζ
    hζ
  refine fltIdeals_coprime ?_ ?_ H (ab_coprime H hpri.out.ne_zero hgcd) hη₁ hη₂ hη caseI
  · exact hpri.out
  · exact h5p
end FltRegular
