-- Prove2me | solution 1 for BlockCycleRotation.K_cf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:51:26.047501+00:00
-- url     : https://prove2.me/submissions/d0962762-e42c-4556-85e7-68ef9d7cfc95

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cf_of_pos {a a' : ℕ} (h : a' ≠ 0) :
    cf a a' = cf a' (a % a') ++ [a / a'] := by rw [cf]; simp [h]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Heilbronn's correspondence, inverse direction.**  Every coprime pair
`a > a' ≥ 1` is `(K l, K l.dropLast)` for the expansion `l = cf a a'`. -/
theorem solution : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    K (cf a a') = a ∧ K (cf a a').dropLast = a':= by
  intro a'
  induction a' using Nat.strong_induction_on with
  | _ a' ih =>
    intro a ha'1 hlt hgcd
    rcases Nat.lt_or_ge a' 2 with h2 | h2
    · -- `a' = 1`: the expansion is the single entry `a`
      have ha'eq : a' = 1 := by omega
      subst ha'eq
      have h1 : cf a 1 = [a] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      simp
    · -- `a' ≥ 2`: peel off the quotient and recurse
      have ha'ne : a' ≠ 0 := by omega
      have hrlt : a % a' < a' := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ a % a' := by
        rcases Nat.eq_zero_or_pos (a % a') with h0 | h0
        · exfalso
          have hdvd : a' ∣ a := Nat.dvd_of_mod_eq_zero h0
          have hg : Nat.gcd a a' = a' := Nat.gcd_eq_right hdvd
          omega
        · exact h0
      have hgcd' : Nat.gcd a' (a % a') = 1 := by
        rw [← hgcd, Nat.gcd_comm a a', Nat.gcd_rec a' a]
        exact Nat.gcd_comm _ _
      obtain ⟨hK, hKd⟩ := ih (a % a') hrlt a' hr1 hrlt hgcd'
      have hne : cf a' (a % a') ≠ [] := by
        intro hc
        rw [hc] at hK
        simp at hK
        omega
      have hcf : cf a a' = cf a' (a % a') ++ [a / a'] := cf_of_pos ha'ne
      constructor
      · rw [hcf, K_concat _ hne (a / a'), hK, hKd]
        have hdm := Nat.div_add_mod a a'
        have hcomm : a / a' * a' = a' * (a / a') := Nat.mul_comm _ _
        omega
      · rw [hcf]
        simpa using hK
