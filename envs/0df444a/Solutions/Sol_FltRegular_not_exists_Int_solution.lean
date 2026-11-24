-- Prove2me | solution 1 for FltRegular.not_exists_Int_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:18.621376+00:00
-- url     : https://prove2.me/submissions/384419a7-3743-4cd3-bbcf-275ee9bb211d

module
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_CaseII_Statement
public import Theorems.Thm_P2M_FltRegular_not_exists_solution__cd5a77927ad8

set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open FltRegular
namespace FltRegular
theorem _root_.solution {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ¬↑p ∣ y ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField p ℚ)) (Set.mem_singleton p) hpri.1.ne_zero
  have := fun n ↦ IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
    (K := CyclotomicField p ℚ) p hζ (n := n)
  simp_rw [← this]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  refine not_exists_solution' (K := CyclotomicField p ℚ) hodd ?_
    hζ ⟨x, y, z, hy, hz, ?_, ?_⟩
  · simpa [IsRegularPrime, IsRegularNumber] using hreg
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]
end FltRegular
