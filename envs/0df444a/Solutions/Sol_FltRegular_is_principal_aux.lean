-- Prove2me | solution 1 for FltRegular.is_principal_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:16.448792+00:00
-- url     : https://prove2.me/submissions/665e6896-e97c-4550-8e90-a882e6dfdc1e

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement

set_option autoImplicit false
@[expose] public section
public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
open FltRegular
variable {p : ℕ}
local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K
namespace FltRegular
theorem _root_.solution {K' : Type*} [Field K'] [CharZero K'] [IsCyclotomicExtension {p} ℚ K']
    [Fintype (ClassGroup (𝓞 K'))]
    {a b : ℤ} {ζ : 𝓞 K'} (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K'))
    {I : Ideal (𝓞 K')} (hI : span ({↑a + ζ * ↑b} : Set (𝓞 K')) = I ^ p) :
    ∃ (u : (𝓞 K')ˣ) (α : 𝓞 K'), ↑u * α ^ p = ↑a + ζ * ↑b := by
  let : NumberField K' := IsCyclotomicExtension.numberField {p} ℚ K'
  obtain ⟨α, hα⟩ : I.IsPrincipal := by
    apply Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hreg
    exact ⟨⟨↑a + ζ * ↑b, by rw [submodule_span_eq, hI]⟩⟩
  replace hα := congr_arg (fun (J : Submodule _ _) ↦ J ^ p) hα
  simp only [← hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα
  obtain ⟨u, hu⟩ := hα
  refine ⟨u⁻¹, α, ?_⟩
  rw [← hu, mul_comm ((_ + ζ * _)), Units.inv_mul_cancel_left]
end FltRegular
