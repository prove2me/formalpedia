-- Prove2me | solution 1 for BandParity.two_eq_generator_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:00.407314+00:00
-- url     : https://prove2.me/submissions/dcf572a5-8a94-44a6-9cc7-9ca37f00cda1

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
omit hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    ∃ e : ℕ, Odd e ∧ ((g ^ e : (ZMod p)ˣ) : ZMod p) = 2 := by
  have hp2 : p ≠ 2 := by omega
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
    exact hp2 this
  obtain ⟨e, he⟩ := hg (Units.mk0 2 h20)
  refine ⟨e, ?_, by rw [he]; rfl⟩
  rcases Nat.even_or_odd e with ⟨j, rfl⟩ | h
  · exfalso
    have hsq : IsSquare (2 : ZMod p) := ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), by
      rw [← Units.val_mul, ← pow_add, he]; rfl⟩
    rcases (ZMod.exists_sq_eq_two_iff hp2).1 hsq with h | h <;> omega
  · exact h
end BandParity
