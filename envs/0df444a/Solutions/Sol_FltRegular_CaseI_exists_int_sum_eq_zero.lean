-- Prove2me | solution 1 for FltRegular.CaseI.exists_int_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:19.112035+00:00
-- url     : https://prove2.me/submissions/dd934a6b-46d4-4b74-8628-df813fbab285

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Theorems.Thm_P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a

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
namespace FltRegular.CaseI
theorem _root_.solution (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ x y i h hp
  refine ⟨k, ?_⟩
  have hz : ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) = (zetaUnit ^ (2 * (k : ℤ)) : (𝓞 K)ˣ) := by
    rw [← zpow_natCast (zetaUnit ^ k) 2, ← zpow_natCast zetaUnit k, ← zpow_mul]
    congr 1
    exact mul_comm _ _
  exact hz ▸ hk
end FltRegular.CaseI
