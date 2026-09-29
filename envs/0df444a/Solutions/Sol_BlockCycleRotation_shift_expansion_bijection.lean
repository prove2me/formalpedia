-- Prove2me | solution 1 for BlockCycleRotation.shift_expansion_bijection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:55:10.950719+00:00
-- url     : https://prove2.me/submissions/4b6da408-d844-452f-b325-82f699c94679

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_coprime
import Theorems.Thm_BlockCycleRotation_K_pos
import Theorems.Thm_BlockCycleRotation_K_cf
import Theorems.Thm_BlockCycleRotation_cf_K
import Theorems.Thm_BlockCycleRotation_cf_spec
import Theorems.Thm_BlockCycleRotation_two_mul_K_dropLast_le
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

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cf_of_pos {a a' : ℕ} (h : a' ≠ 0) :
    cf a a' = cf a' (a % a') ++ [a / a'] := by rw [cf]; simp [h]

/-- The last entry of `cf n k` is the first Euclidean quotient. -/
theorem cf_getLast {n k : ℕ} (hk : k ≠ 0) : (cf n k).getLast? = some (n / k) := by
  rw [cf_of_pos hk]
  simp

/-- If `2k ≤ n` the expansion's last entry is at least `2`. -/
theorem two_le_cf_getLast {n k : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ n) :
    ∀ x ∈ (cf n k).getLast?, 2 ≤ x := by
  intro x hx
  rw [cf_getLast hk] at hx
  simp at hx
  subst hx
  exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hk)).2 (by omega)

end BlockCycleRotation

open BlockCycleRotation in
/-- **The shift–expansion bijection.**

For each `n`, the map `k ↦ cf n k` sends the shifts `1 ≤ k` with `2k ≤ n` and
`gcd(n,k) = 1` — exactly the range the block cycle algorithm recurses on — to
the normalised expansions of `n` whose last entry is at least `2`, i.e. exactly
Heilbronn's index set.  The inverse is `L ↦ K L.dropLast`.

The first component says the forward map lands correctly and is inverted by
`L ↦ K L.dropLast`; the second says the backward map lands correctly and is
inverted by `k ↦ cf n k`. -/
theorem solution (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → Nat.gcd n k = 1 →
        K (cf n k) = n ∧ K (cf n k).dropLast = k ∧ cf n k ≠ []
          ∧ (∀ c ∈ cf n k, 1 ≤ c) ∧ (∀ x ∈ (cf n k).head?, 2 ≤ x)
          ∧ (∀ x ∈ (cf n k).getLast?, 2 ≤ x))
      ∧ (∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) → (∀ x ∈ L.head?, 2 ≤ x) →
        (∀ x ∈ L.getLast?, 2 ≤ x) →
          cf (K L) (K L.dropLast) = L ∧ 1 ≤ K L.dropLast
            ∧ 2 * K L.dropLast ≤ K L ∧ Nat.gcd (K L) (K L.dropLast) = 1):= by
  constructor
  · intro k hk1 hk2 hgcd
    have hkn : k < n := by omega
    have hkne : k ≠ 0 := by omega
    obtain ⟨hK, hKd⟩ := K_cf k n hk1 hkn hgcd
    obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
    exact ⟨hK, hKd, hne, hpos, hhead, two_le_cf_getLast hkne hk2⟩
  · intro L hne hpos hhead hlast
    refine ⟨cf_K L hne hpos hhead, ?_, two_mul_K_dropLast_le L hne hpos hlast,
      K_coprime L⟩
    exact K_pos _ (fun x hx => hpos x (List.dropLast_subset L hx))
