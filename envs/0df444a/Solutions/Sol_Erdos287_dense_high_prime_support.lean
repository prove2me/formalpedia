-- Prove2me | solution 1 for Erdos287.dense_high_prime_support
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:25:41.437413+00:00
-- url     : https://prove2.me/submissions/523be2aa-d763-44d0-bd85-92ad8e7790f1

import Mathlib
import Theorems.Thm_Erdos287_short_cofactor_layer
import Theorems.Thm_Erdos287_high_cofactor_exclusions

open Finset

set_option autoImplicit false

/-- In the dense ratio range, a prime power above one third of the interval
diameter can occur only in the five listed cofactor patterns. -/
theorem solution (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hratio : M < 3 * m) (hspread : 5 * m ≤ 2 * M) (hspan : M < m + 3 * p ^ e) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨
      (p = 3 ∧ H = {q, 2 * q}) ∨
      (p = 5 ∧ H = {2 * q, 3 * q}) ∨
      (p = 7 ∧ H = {3 * q, 4 * q}) ∨
      (p = 3 ∧ H = {2 * q, 4 * q}) ∨
      (p = 13 ∧ H = {2 * q, 3 * q, 4 * q}) := by
  let q := p ^ e
  let H := D.filter (fun n => q ∣ n)
  change H = ∅ ∨
      (p = 3 ∧ H = {q, 2 * q}) ∨
      (p = 5 ∧ H = {2 * q, 3 * q}) ∨
      (p = 7 ∧ H = {3 * q, 4 * q}) ∨
      (p = 3 ∧ H = {2 * q, 4 * q}) ∨
      (p = 13 ∧ H = {2 * q, 3 * q, 4 * q})
  change M < m + 3 * q at hspan
  have hM : M < 5 * q := by omega
  by_cases hp2 : p = 2
  · subst p
    exact Or.inl ((Erdos287.high_cofactor_exclusions D m M hm hD hsum).1 e he hratio hM)
  have hnot2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  have hwindow (a b : ℕ) (ha : m ≤ a * q) (hb : b * q ≤ M) : b ≤ a + 2 := by
    have hscale : b * q < (a + 3) * q := by rw [add_mul]; omega
    have hb' := Nat.lt_of_mul_lt_mul_right hscale
    omega
  have hup (b : ℕ) (hb : b * q ∈ H) : b < 5 :=
    Nat.lt_of_mul_lt_mul_right ((mem_Icc.mp (hD (mem_filter.mp hb).1)).2.trans_lt hM)
  have hforbid (h₁ : q ∈ H) (h₃ : 3 * q ∈ H) : False := by
    have h₁' := (mem_Icc.mp (hD (mem_filter.mp h₁).1)).1
    have h₃' := (mem_Icc.mp (hD (mem_filter.mp h₃).1)).2
    omega
  rcases Erdos287.short_cofactor_layer D m M p e hm hp he hD hsum hwindow with
    h | ⟨c, hc, hs⟩
  · exact Or.inl h
  · rcases hs with ⟨hpair, hd⟩ | ⟨hpair, hd⟩ | ⟨htriple, hd⟩
    · have hpair' : H = {c * q, (c + 1) * q} := hpair
      have h := hup (c + 1) (by rw [hpair']; simp)
      have hcu : c ≤ 3 := by omega
      interval_cases c
      · have hp' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (by simpa using hd)
        exact Or.inr (Or.inl ⟨hp', by simpa using hpair'⟩)
      · have hp' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (by simpa using hd)
        exact Or.inr (Or.inr (Or.inl ⟨hp', by simpa using hpair'⟩))
      · have hp' : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (by simpa using hd)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp', by simpa using hpair'⟩)))
    · have hpair' : H = {c * q, (c + 2) * q} := hpair
      have h := hup (c + 2) (by rw [hpair']; simp)
      have hcu : c ≤ 2 := by omega
      interval_cases c
      · exact (hforbid (by rw [hpair']; simp) (by rw [hpair']; simp)).elim
      · have hd' : p ∣ 2 * 3 := by simpa using hd
        have hp' := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
          ((hp.dvd_mul.mp hd').resolve_left hnot2)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp', by simpa using hpair'⟩))))
    · have htriple' : H = {c * q, (c + 1) * q, (c + 2) * q} := htriple
      have h := hup (c + 2) (by rw [htriple']; simp)
      have hcu : c ≤ 2 := by omega
      interval_cases c
      · exact (hforbid (by rw [htriple']; simp) (by rw [htriple']; simp)).elim
      · have hd' : p ∣ 2 * 13 := by simpa using hd
        have hp' := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp
          ((hp.dvd_mul.mp hd').resolve_left hnot2)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp', by simpa using htriple'⟩))))

