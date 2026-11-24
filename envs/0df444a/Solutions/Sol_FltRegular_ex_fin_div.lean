-- Prove2me | solution 1 for FltRegular.ex_fin_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:12.706671+00:00
-- url     : https://prove2.me/submissions/f84e076a-8229-4a8f-ab31-fd0a69afdfb8

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Theorems.Thm_FltRegular_is_principal
public import Theorems.Thm_FltRegular_CaseI_exists_int_sum_eq_zero


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
theorem _root_.solution {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hreg : IsRegularPrime p)
    (hζ : IsPrimitiveRoot ζ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) (H : a ^ p + b ^ p = c ^ p) :
    ∃ k₁ k₂ : Fin p,
      k₂ ≡ k₁ - 1 [ZMOD p] ∧
        ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let zetaUnit := (hζ'.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have h : ζ = (zetaUnit : R) := by rfl
  have hP : p ≠ 2 := by
    intro hP
    rw [hP] at hp5
    contradiction
  obtain ⟨u, α, hu⟩ := is_principal hreg hp5 hgcd caseI H hζ
  rw [h, mul_comm _ (↑b : R), ← pow_one zetaUnit] at hu
  obtain ⟨k, hk⟩ := FltRegular.CaseI.exists_int_sum_eq_zero hζ' a b 1 hu.symm (by lia)
  simp only [zpow_one, zpow_neg, mem_span_singleton] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by simp [hpri.out.ne_zero]
  have hζ_map : (algebraMap R K) ζ = ζ' := rfl
  refine ⟨⟨(2 * k % p).natAbs, ?_⟩, ⟨((2 * k - 1) % p).natAbs, ?_⟩, ?_, ?_⟩
  repeat'
    rw [← natAbs_natCast p]
    refine natAbs_lt_natAbs_of_nonneg_of_lt (emod_nonneg _ hpcoe) ?_
    rw [natAbs_natCast]
    exact emod_lt_of_pos _ (by simp [hpri.out.pos])
  · simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_eq_intCast_iff,
      ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, Int.cast_one]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert! hk using 3
  rw [mul_add, mul_comm (↑a : R), ← mul_assoc _ (↑b : R), mul_comm _ (↑b : R),
    mul_assoc (↑b : R)]
  congr 2
  · ext
    simp only [map_pow, NumberField.Units.coe_zpow, hζ_map]
    change ζ' ^ ↑(2 * k % ↑p).natAbs = ζ' ^ (2 * k)
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, sub_self]
  · ext
    simp only [map_pow, _root_.map_mul, NumberField.Units.coe_zpow, map_units_inv, hζ_map]
    change ζ' ^ ↑((2 * k - 1) % ↑p).natAbs = ζ' ^ (2 * k) * ζ'⁻¹
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, Int.cast_one, sub_self]
end FltRegular
