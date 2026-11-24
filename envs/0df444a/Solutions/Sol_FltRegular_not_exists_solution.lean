-- Prove2me | solution 1 for FltRegular.not_exists_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:46.708802+00:00
-- url     : https://prove2.me/submissions/fc12e8be-54d4-4339-abe6-9dba133a1e20

module
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_CaseII_Statement
public import Theorems.Thm_P2M_exists_solution__12b540d0a90c
public import Theorems.Thm_one_le_m


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
include hp hreg
namespace FltRegular
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
  ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬((hζ.toInteger : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
    x' ^ p + y' ^ p = ε₃ * (((hζ.toInteger : 𝓞 K) - 1) ^ m * z') ^ p := by
  induction m, hm using Nat.le_induction with
  | base =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact zero_lt_one.not_ge (one_le_m hp hζ e hy hz)
  | succ m' _ IH =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact IH (exists_solution' hp hζ e hy hz hreg)
end FltRegular
