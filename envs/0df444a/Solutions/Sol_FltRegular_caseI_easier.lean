-- Prove2me | solution 1 for FltRegular.caseI_easier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:00.19295+00:00
-- url     : https://prove2.me/submissions/79bc37a9-d9a4-4ad8-9644-bfc5a4428b50

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Theorems.Thm_FltRegular_ex_fin_div
public import Theorems.Thm_dvd_coeff_cycl_integer

section
@[expose] public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
namespace FltRegular
variable {p : ℕ}
namespace CaseI
end CaseI
private theorem sum_caseICoeff {R : Type*} [Ring R] (hp : 1 < p) (a b : ℤ)
    (k₁ k₂ : Fin p) (ζ : R) :
    ∑ j : Fin p, caseICoeff a b k₁ k₂ j • ζ ^ (j : ℕ) =
      ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ caseICoeff a b k₁ k₂ j • ζ ^ j) p]
  simp only [caseICoeff, add_smul, sub_smul, ite_smul, sum_add_distrib,
    sum_sub_distrib, sum_ite, Finset.range_filter_eq]
  simp [Nat.zero_lt_of_lt hp, hp, Fin.is_lt]
private theorem exists_caseICoeff_eq_zero (hp5 : 5 ≤ p) (a b : ℤ)
    (k₁ k₂ : Fin p) : ∃ j : Fin p, caseICoeff a b k₁ k₂ j = 0 := by
  let zero : Fin p := ⟨0, by lia⟩
  let one : Fin p := ⟨1, by lia⟩
  let s : Finset (Fin p) := {zero, one, k₁, k₂}
  have hs : s.card ≤ 4 := card_le_four
  have hslt : s.card < Fintype.card (Fin p) := by
    simpa using lt_of_le_of_lt hs hp5
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hslt
  refine ⟨j, ?_⟩
  simp only [s, mem_insert, mem_singleton, not_or] at hj
  have hj0 : (j : ℕ) ≠ 0 := fun h ↦ hj.1 (Fin.ext h)
  have hj1 : (j : ℕ) ≠ 1 := fun h ↦ hj.2.1 (Fin.ext (by simpa [one] using h))
  have hjk₁ : (j : ℕ) ≠ k₁ := fun h ↦ hj.2.2.1 (Fin.ext h)
  have hjk₂ : (j : ℕ) ≠ k₂ := fun h ↦ hj.2.2.2 (Fin.ext h)
  simp [caseICoeff, hj0, hj1, hjk₁, hjk₂]
local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K
variable [hpri : Fact p.Prime]
end FltRegular
end
end

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
theorem _root_.solution {a b c : ℤ} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hab : ¬a ≡ b [ZMOD p])
    (caseI : ¬↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  set ζ := zeta p ℤ R
  have hζ := zeta_spec p ℤ R
  intro H
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := ex_fin_div hp5 hreg hζ hgcd caseI H
  have key :
      ↑(p : ℤ) ∣ ∑ j : Fin p, caseICoeff a b k₁ k₂ j • ζ ^ (j : ℕ) := by
    rw [sum_caseICoeff hpri.out.one_lt]
    exact hdiv
  have hall := dvd_coeff_cycl_integer hpri.out hζ
    (exists_caseICoeff_eq_zero hp5 a b k₁ k₂) key
  by_cases hk₁ : (k₁ : ℕ) = 0
  · have hk₂ : (k₂ : ℕ) ≠ 1 := by
      intro hk₂
      have hp2z : (p : ℤ) ∣ 2 := by
        rw [← Int.dvd_neg]
        simpa [hk₁, hk₂] using hcong.dvd
      have hple2 := Nat.le_of_dvd two_pos (by exact_mod_cast hp2z : p ∣ 2)
      omega
    have hb : (p : ℤ) ∣ b := by
      simpa [caseICoeff, hk₁, hk₂, Ne.symm hk₂] using hall ⟨1, by lia⟩
    exact caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_left hb a) c)
  · by_cases hk₂ : (k₂ : ℕ) = 0
    · have habdvd : (p : ℤ) ∣ a - b := by
        simpa [caseICoeff, hk₁, Ne.symm hk₁, hk₂] using hall ⟨0, by lia⟩
      apply hab
      rw [Int.modEq_iff_dvd]
      simpa only [neg_sub] using Int.dvd_neg.mpr habdvd
    · have ha : (p : ℤ) ∣ a := by
        simpa [caseICoeff, hk₁, hk₂, Ne.symm hk₁, Ne.symm hk₂] using hall ⟨0, by lia⟩
      exact caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ha b) c)
end FltRegular
