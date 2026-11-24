-- Prove2me | solution 1 for FltRegular.CaseI.may_assume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:14.464863+00:00
-- url     : https://prove2.me/submissions/09fdcebf-7f42-4710-8406-f551131cce4d

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Theorems.Thm_FltRegular_MayAssume_coprime
public import Theorems.Thm_FltRegular_a_not_cong_b


set_option autoImplicit false
@[expose] public section
public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
open FltRegular
variable {p : ℕ}
open FltRegular.CaseI
namespace FltRegular.CaseI
theorem _root_.solution : SlightlyEasier → Statement := by
  intro Heasy a b c p hpri hreg hI H
  have hodd : p ≠ 2 := by
    rintro rfl
    refine hI <| Dvd.dvd.mul_left ?_ _
    simp only [Nat.cast_ofNat, ← even_iff_two_dvd] at hI ⊢
    rw [Int.not_even_iff_odd] at hI
    rw [← Int.even_pow' two_ne_zero, ← H]
    exact (Odd.of_mul_left (Odd.of_mul_left hI)).pow.add_odd
      (Odd.of_mul_right (Odd.of_mul_left hI)).pow
  have hprod : a * b * c ≠ 0 := by
    intro h
    simp [h] at hI
  have hp5 : 5 ≤ p := by
    by_contra! habs
    have : 2 < p := Nat.lt_of_le_of_ne hpri.out.two_le hodd.symm
    interval_cases p
    · exact fermatLastTheoremFor_iff_int.1 fermatLastTheoremThree a b c
        (fun ha ↦ hprod <| by simp [ha]) (fun hb ↦ hprod <| by simp [hb])
        (fun hc ↦ hprod <| by simp [hc]) H
    · exact Nat.not_prime_mul one_lt_two.ne' one_lt_two.ne' hpri.out
  let d := ({a, b, c} : Finset ℤ).gcd id
  have hdiv : ¬↑p ∣ a / d * (b / d) * (c / d) := by
    contrapose hI with hdiv
    have hadiv : d ∣ a := gcd_dvd (by simp)
    have hbdiv : d ∣ b := gcd_dvd (by simp)
    have hcdiv : d ∣ c := gcd_dvd (by simp)
    rw [← Int.ediv_mul_cancel hadiv, ← Int.ediv_mul_cancel hbdiv, ← Int.ediv_mul_cancel hcdiv]
    convert! dvd_mul_of_dvd_right hdiv (d * d * d) using 1
    grind
  rcases MayAssume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩
  obtain ⟨_, _, _, H1, H2, H3, _, H5⟩ :=
    a_not_cong_b hpri.out hp5 hprodxyx Hxyz hunit hdiv
  exact Heasy hreg hp5 H2 H3 H5 H1
end FltRegular.CaseI
