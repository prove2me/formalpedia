-- Prove2me | solution 1 for BlockCycleRotation.cf_K
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:51:46.998598+00:00
-- url     : https://prove2.me/submissions/d9f91efb-e03c-4998-ae27-7575bf728980

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_pos
import Theorems.Thm_BlockCycleRotation_K_dropLast_lt_prime
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
/-- **Heilbronn's correspondence, injectivity.**  A normalised expansion is
recovered from its pair of continuants.

Normalisation is `2 ≤ c₀`: without it `[1, c]` and `[c+1]` have the same pair,
which is the familiar ambiguity of continued fractions. -/
theorem solution : ∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
    cf (K l) (K l.dropLast) = l:= by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton m c ih =>
    intro _ hpos hhead
    rcases m with _ | ⟨d, ds⟩
    · -- `l = [c]`, normalised means `2 ≤ c`
      have hc2 : 2 ≤ c := hhead c (by simp)
      simp only [List.nil_append]
      rw [K_singleton, show ([c] : List ℕ).dropLast = [] from by simp, K_nil,
        cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
      simp
    · set m := d :: ds with hm
      have hmne : m ≠ [] := by simp [hm]
      have hmpos : ∀ x ∈ m, 1 ≤ x := fun x hx => hpos x (List.mem_append.2 (Or.inl hx))
      have hhead_d : 2 ≤ d := by
        apply hhead d
        rw [hm]
        simp
      have hmhead : ∀ x ∈ m.head?, 2 ≤ x := by
        intro x hx
        rw [hm] at hx
        simp at hx
        omega
      have hsingle : m.length = 1 → 2 ≤ K m := by
        intro h1
        obtain ⟨e, he⟩ := List.length_eq_one_iff.1 h1
        rw [he, K_singleton]
        exact hmhead e (by rw [he]; simp)
      have hlt : K m.dropLast < K m := K_dropLast_lt_prime hmne hmpos hsingle
      have hKmpos : K m ≠ 0 := by
        have := K_pos m hmpos
        omega
      have hdl : (m ++ [c]).dropLast = m := by simp
      rw [K_concat m hmne c, hdl,
        show c * K m + K m.dropLast = K m.dropLast + K m * c from by ring,
        cf_of_pos hKmpos, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ (by omega : 0 < K m), Nat.div_eq_of_lt hlt,
        Nat.zero_add, ih hmne hmpos hmhead]
