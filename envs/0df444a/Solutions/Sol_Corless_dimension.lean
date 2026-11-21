-- Prove2me | solution 1 for Corless.dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:36.683177+00:00
-- url     : https://prove2.me/submissions/1db9bcbc-ce79-4907-910b-6e7b1dc3faed

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_Dv_parity
public import Theorems.Thm_Corless_two_eq_zero_Z2X
public import Theorems.Thm_Corless_fbar_comp
public import Theorems.Thm_Corless_pow_two_of_frob
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s : ℕ → ℤ} {m : ℕ} (hs : IsSign s m) (hm : 1 ≤ m) (h : Dv s m = 1) :
    ∃ k, m = 2 ^ (k + 1) - 1 := by
  obtain ⟨R, hR⟩ := Dv_parity m hs
  have hf : fbar m = 1 := by
    have : f m = 1 - 2 * R := by rw [← h, hR]; ring
    have h2 : Polynomial.map (Int.castRingHom (ZMod 2)) (2 : ℤ[X]) = 2 := by simp
    simp only [fbar, this, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, h2,
      two_eq_zero_Z2X, zero_mul, sub_zero]
  have hc := fbar_comp m
  rw [hf, one_comp] at hc
  have h2 : (1 + X : (ZMod 2)[X]) ^ (m + 1) = 1 + X ^ (m + 1) := by
    linear_combination (-1 : (ZMod 2)[X]) * hc - X ^ (m + 1) * two_eq_zero_Z2X
  obtain ⟨a, ha⟩ := pow_two_of_frob (m + 1) (by omega) h2
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at ha; omega
    · exact h0
  exact ⟨a - 1, by rw [show a - 1 + 1 = a by omega]; omega⟩
end Corless
