-- Prove2me | solution 1 for FltRegular.CaseI.pow_sub_intGalConj_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:36.465069+00:00
-- url     : https://prove2.me/submissions/2f6de3e5-b68d-4b29-8330-1b3e53d98638

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Theorems.Thm_exists_dvd_pow_sub_Int_pow


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
open FractionalIdeal NumberField IsCMField
open FltRegular FltRegular.CaseI
omit [NeZero p]
namespace FltRegular.CaseI
theorem _root_.solution (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨a, γ, hγ⟩ := exists_dvd_pow_sub_Int_pow hp.ne' α
  rw [Ideal.mem_span_singleton]
  rw [sub_eq_iff_eq_add] at hγ
  rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_pow, map_intCast,
    add_sub_add_right_eq_sub, ← mul_sub]
  exact dvd_mul_right _ _
end FltRegular.CaseI
