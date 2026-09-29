-- Prove2me | solution 1 for BlockCycleRotation.split_quadruple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:58:14.747266+00:00
-- url     : https://prove2.me/submissions/30bfc248-092f-40ce-ad97-02f9dffce1ec

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_K_coprime
import Theorems.Thm_BlockCycleRotation_K_pos
import Theorems.Thm_BlockCycleRotation_K_dropLast_lt_prime
import Theorems.Thm_BlockCycleRotation_K_tail_lt_prime
import Theorems.Thm_BlockCycleRotation_K_cf
import Theorems.Thm_BlockCycleRotation_cf_spec
import Theorems.Thm_BlockCycleRotation_getLast_opt_drop_of_getLast_opt
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

/-- The prefix continuants are coprime, mirrored to suffixes. -/
theorem K_coprime_tail (l : List ℕ) : Nat.gcd (K l) (K l.tail) = 1 := by
  have hrev : (l.reverse).dropLast = (l.tail).reverse := by
    rcases l with _ | ⟨a, t⟩ <;> simp
  have h := K_coprime l.reverse
  rwa [hrev, K_reverse, K_reverse] at h

/-- **Heilbronn's correspondence, forward direction.**  The quadruple obtained by
splitting an expansion satisfies `n = a·b + a'·b'`, the size conditions
`a > a' ≥ 1` and `b > b' ≥ 1`, and the coprimality conditions. -/
theorem heilbronn_forward {l₁ l₂ : List ℕ} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hpos₁ : ∀ c ∈ l₁, 1 ≤ c) (hpos₂ : ∀ c ∈ l₂, 1 ≤ c)
    (hfirst : l₁.length = 1 → 2 ≤ K l₁) (hlast : l₂.length = 1 → 2 ≤ K l₂) :
    K (l₁ ++ l₂) = K l₁ * K l₂ + K l₁.dropLast * K l₂.tail ∧
      K l₁.dropLast < K l₁ ∧ 1 ≤ K l₁.dropLast ∧
      K l₂.tail < K l₂ ∧ 1 ≤ K l₂.tail ∧
      Nat.gcd (K l₁) (K l₁.dropLast) = 1 ∧
      Nat.gcd (K l₂) (K l₂.tail) = 1 := by
  refine ⟨K_append l₁ l₂ h₁ h₂, K_dropLast_lt_prime h₁ hpos₁ hfirst, ?_,
    K_tail_lt_prime h₂ hpos₂ hlast, ?_, K_coprime l₁, K_coprime_tail l₂⟩
  · exact K_pos _ (fun x hx => hpos₁ x (List.dropLast_subset l₁ hx))
  · exact K_pos _ (fun x hx => hpos₂ x (List.tail_subset l₂ hx))

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

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

/-- A one-element list has `K` equal to its entry, so a head condition gives a
lower bound on `K`. -/
theorem two_le_K_of_length_one {l : List ℕ} (h : l.length = 1)
    (hhead : ∀ x ∈ l.head?, 2 ≤ x) : 2 ≤ K l := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  subst hc
  simpa using hhead c (by simp)

/-- The same from a last-entry condition. -/
theorem two_le_K_of_length_one_prime {l : List ℕ} (h : l.length = 1)
    (hlast : ∀ x ∈ l.getLast?, 2 ≤ x) : 2 ≤ K l := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  subst hc
  simpa using hlast c (by simp)

/-- A prefix inherits the head condition. -/
theorem head_opt_take_of_head_opt {L : List ℕ} {j : ℕ} (hj : 1 ≤ j)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) : ∀ x ∈ (L.take j).head?, 2 ≤ x := by
  intro x hx
  apply hhead
  rcases L with _ | ⟨a, t⟩
  · simp at hx
  · rcases j with _ | j'
    · omega
    · simp at hx ⊢
      omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The quadruple produced by a split.**  For a shift `k` the algorithm
recurses on and an interior split point `j`, the four continuants satisfy every
condition defining Heilbronn's target set. -/
theorem solution {n k j : ℕ} (hk : k ∈ shifts n) (hj1 : 1 ≤ j)
    (hj2 : j < (cf n k).length) :
    n = K ((cf n k).take j) * K ((cf n k).drop j)
        + K ((cf n k).take j).dropLast * K ((cf n k).drop j).tail
      ∧ 1 ≤ K ((cf n k).take j).dropLast
      ∧ K ((cf n k).take j).dropLast < K ((cf n k).take j)
      ∧ 1 ≤ K ((cf n k).drop j).tail
      ∧ K ((cf n k).drop j).tail < K ((cf n k).drop j)
      ∧ Nat.gcd (K ((cf n k).take j)) (K ((cf n k).take j).dropLast) = 1
      ∧ Nat.gcd (K ((cf n k).drop j)) (K ((cf n k).drop j).tail) = 1:= by
  obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
  have hkn : k < n := by omega
  have hkne : k ≠ 0 := by omega
  obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
  have hlast := two_le_cf_getLast hkne hk2
  have hKn : K (cf n k) = n := (K_cf k n hk1 hkn hgcd).1
  -- the two halves
  have hne₁ : (cf n k).take j ≠ [] := by
    intro hc
    have hl : ((cf n k).take j).length = 0 := by rw [hc]; simp
    rw [List.length_take] at hl
    omega
  have hne₂ : (cf n k).drop j ≠ [] := by
    intro hc
    have hl : ((cf n k).drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hpos₁ : ∀ c ∈ (cf n k).take j, 1 ≤ c := fun c hc => hpos c (List.take_subset j _ hc)
  have hpos₂ : ∀ c ∈ (cf n k).drop j, 1 ≤ c := fun c hc => hpos c (List.drop_subset j _ hc)
  have hfirst : ((cf n k).take j).length = 1 → 2 ≤ K ((cf n k).take j) := fun h =>
    two_le_K_of_length_one h (head_opt_take_of_head_opt hj1 hhead)
  have hlast' : ((cf n k).drop j).length = 1 → 2 ≤ K ((cf n k).drop j) := fun h =>
    two_le_K_of_length_one_prime h (getLast_opt_drop_of_getLast_opt hj2 hlast)
  obtain ⟨hsum, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    heilbronn_forward hne₁ hne₂ hpos₁ hpos₂ hfirst hlast'
  refine ⟨?_, h₂, h₁, h₄, h₃, h₅, h₆⟩
  rw [List.take_append_drop, hKn] at hsum
  exact hsum
