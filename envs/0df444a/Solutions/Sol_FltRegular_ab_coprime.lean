-- Prove2me | solution 1 for FltRegular.ab_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:57.847868+00:00
-- url     : https://prove2.me/submissions/25607495-c4c4-415a-9b03-8c6ae08c5666

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
namespace FltRegular
theorem _root_.solution {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) : IsCoprime a b := by
  rw [isCoprime_iff_gcd_eq_one]
  by_contra! h
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h
  replace hqpri : Prime (q : ℤ) := prime_iff_natAbs_prime.2 (by simp [hqpri])
  have haq : ↑q ∣ a := (Int.natCast_dvd_natCast.2 hq).trans (Int.gcd_dvd_left a b)
  have hbq : ↑q ∣ b := (Int.natCast_dvd_natCast.2 hq).trans (Int.gcd_dvd_right a b)
  have hcq : ↑q ∣ c :=
    hqpri.dvd_of_dvd_pow (H ▸ dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero))
  have Hq : ↑q ∣ ({a, b, c} : Finset ℤ).gcd id := by
    refine dvd_gcd fun x hx ↦ ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with H | H | H <;> simpa [H]
  rw [hgcd] at Hq
  exact hqpri.not_isUnit (isUnit_of_dvd_one Hq)
end FltRegular
