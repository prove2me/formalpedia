-- Prove2me | solution 1 for BlockCycleRotation.sum_split_eq_sum_quadruples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:02:23.468044+00:00
-- url     : https://prove2.me/submissions/006c193d-b42a-40c9-8d22-f63bb9813b13

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_K_cf
import Theorems.Thm_BlockCycleRotation_cf_spec
import Theorems.Thm_BlockCycleRotation_split_quadruple
import Theorems.Thm_BlockCycleRotation_heilbronn_split_roundtrip
import Theorems.Thm_BlockCycleRotation_quadExpansion_spec
import Theorems.Thm_BlockCycleRotation_quadExpansion_shift
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

/-- Mirror of the earlier reversal identity. -/
theorem reverse_tail_eq (l : List ℕ) : (l.reverse).tail = (l.dropLast).reverse := by
  have h : ((l.reverse).reverse).dropLast = ((l.reverse).tail).reverse := by
    rcases hl : l.reverse with _ | ⟨a, t⟩ <;> simp
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

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

theorem mem_quadruples {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruples n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ Nat.gcd b b' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruples, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The components of a quadruple are bounded by `n`. -/
theorem quadruple_le {n a b a' b' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : 1 ≤ b')
    (h4 : b' < b) (hsum : n = a * b + a' * b') :
    a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n := by
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Splits land in the quadruple set.** -/
theorem split_mem_quadruples {n k j : ℕ} (hk : k ∈ shifts n) (hj1 : 1 ≤ j)
    (hj2 : j < (cf n k).length) :
    (K ((cf n k).take j), K ((cf n k).drop j),
      K ((cf n k).take j).dropLast, K ((cf n k).drop j).tail) ∈ quadruples n := by
  obtain ⟨hsum, h1, h2, h3, h4, h5, h6⟩ := split_quadruple hk hj1 hj2
  rw [mem_quadruples]
  exact ⟨quadruple_le h1 h2 h3 h4 hsum, h1, h2, h3, h4, h5, h6, hsum⟩

end BlockCycleRotation

open BlockCycleRotation in
/-- **The reindexing of (eq. heilbron).** -/
theorem solution (n : ℕ) :
    ∑ k ∈ shifts n, ∑ j ∈ Finset.Ico 1 (cf n k).length, K ((cf n k).take j)
      = ∑ q ∈ quadruples n, q.1:= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun p _ => (K ((cf n p.1).take p.2), K ((cf n p.1).drop p.2),
      K ((cf n p.1).take p.2).dropLast, K ((cf n p.1).drop p.2).tail))
    (j := fun q _ => (⟨K (quadExpansion q.1 q.2.1 q.2.2.1 q.2.2.2).dropLast,
      (cf q.1 q.2.2.1).length⟩ : (_ : ℕ) × ℕ))
    ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in `quadruples n`
    rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ico] at hp
    exact split_mem_quadruples hp.1 hp.2.1 hp.2.2
  · -- the inverse map lands in the sigma set
    rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨hs, hcf⟩ := quadExpansion_shift hq
    obtain ⟨-, -, -, -, -, -, -, hlen1, hlen2⟩ := quadExpansion_spec hq
    rw [Finset.mem_sigma, Finset.mem_Ico]
    refine ⟨hs, hlen1, ?_⟩
    rw [hcf]
    exact hlen2
  · -- left inverse
    rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ico] at hp
    obtain ⟨hk, hj1, hj2⟩ := hp
    obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
    have hkn : k < n := by omega
    obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
    have hlast := two_le_cf_getLast (by omega : k ≠ 0) hk2
    obtain ⟨h₁, h₂⟩ := heilbronn_split_roundtrip hpos hhead hlast hj1 hj2
    have hLeq : quadExpansion (K ((cf n k).take j)) (K ((cf n k).drop j))
        (K ((cf n k).take j).dropLast) (K ((cf n k).drop j).tail) = cf n k := by
      rw [quadExpansion, h₁, h₂, List.reverse_reverse, List.take_append_drop]
    simp only [hLeq, h₁]
    have hKd : K (cf n k).dropLast = k := (K_cf k n hk1 hkn hgcd).2
    have hjlen : ((cf n k).take j).length = j := by
      rw [List.length_take]
      omega
    rw [hKd, hjlen]
  · -- right inverse
    rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, hcf⟩ := quadExpansion_shift hq
    obtain ⟨-, -, -, -, -, htake, hdrop, -, -⟩ := quadExpansion_spec hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hga, hgb, -⟩ := mem_quadruples.1 hq
    obtain ⟨hKa, hKa'⟩ := K_cf a' a ha1 ha2 hga
    obtain ⟨hKb, hKb'⟩ := K_cf b' b hb1 hb2 hgb
    simp only [hcf, htake, hdrop]
    have e2 : K (cf b b').reverse = b := by rw [K_reverse]; exact hKb
    have e4 : K ((cf b b').reverse).tail = b' := by
      rw [reverse_tail_eq, K_reverse]; exact hKb'
    rw [hKa, e2, hKa', e4]
  · rintro ⟨k, j⟩ _
    rfl
