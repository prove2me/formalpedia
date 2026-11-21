-- Prove2me | solution 1 for Corless.pow_two_of_frob
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:19.875441+00:00
-- url     : https://prove2.me/submissions/d1b57688-8d9f-4652-ae84-d621a4b9702a

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
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
theorem _root_.solution : ∀ n : ℕ, 1 ≤ n → ((1 + X : (ZMod 2)[X]) ^ n = 1 + X ^ n) → ∃ a, n = 2 ^ a
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => ⟨0, by norm_num⟩
  | n + 2, _, h => by
      -- the coefficient of X forces n + 2 to be even
      have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff 1) h
      simp only [coeff_one_add_X_pow, coeff_add, coeff_one, coeff_X_pow] at hc
      have hn1 : (1 : ℕ) ≠ n + 2 := by omega
      simp only [Nat.choose_one_right, one_ne_zero, ite_false, hn1, zero_add] at hc
      have heven : Even (n + 2) := by
        have : ((n + 2 : ℕ) : ZMod 2) = 0 := by exact_mod_cast hc
        rw [ZMod.natCast_eq_zero_iff_even] at this
        exact this
      obtain ⟨r, hr⟩ := heven
      have hr1 : 1 ≤ r := by omega
      -- squares agree, and squaring is injective in characteristic 2
      have hsq : ((1 + X : (ZMod 2)[X]) ^ r) ^ 2 = (1 + X ^ r) ^ 2 := by
        have hfrob : (1 + X ^ r : (ZMod 2)[X]) ^ 2 = 1 + X ^ (r * 2) := by
          have := add_pow_char (R := (ZMod 2)[X]) (p := 2) (1 : (ZMod 2)[X]) (X ^ r)
          rw [one_pow, ← pow_mul] at this
          exact this
        rw [hfrob, ← pow_mul, show r * 2 = n + 2 by omega]
        exact h
      have hr' : (1 + X : (ZMod 2)[X]) ^ r = 1 + X ^ r :=
        frobenius_inj (ZMod 2)[X] 2 hsq
      obtain ⟨a, ha⟩ := solution r hr1 hr'
      exact ⟨a + 1, by rw [pow_succ, ← ha]; omega⟩
end Corless
