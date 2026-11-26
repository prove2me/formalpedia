-- Prove2me | solution 1 for Erdos287.short_cofactor_layer
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:19:34.094575+00:00
-- url     : https://prove2.me/submissions/ae32d9c6-dadc-441e-9260-026e1c34ba97

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence

open Finset

set_option autoImplicit false

/-- If the candidate cofactors of a prime-power layer fit in a window of
three consecutive integers, its nonempty patterns obey a linear or
quadratic congruence. -/
theorem solution (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hwindow : ∀ a b : ℕ, m ≤ a * p ^ e → b * p ^ e ≤ M → b ≤ a + 2) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ ∃ c : ℕ, 0 < c ∧
      ((H = {c * q, (c + 1) * q} ∧ p ∣ 2 * c + 1) ∨
       (H = {c * q, (c + 2) * q} ∧ p ∣ 2 * c + 2) ∨
       (H = {c * q, (c + 1) * q, (c + 2) * q} ∧ p ∣ 3 * c ^ 2 + 6 * c + 2)) := by
  classical
  let q := p ^ e
  let H := D.filter (fun n => q ∣ n)
  change H = ∅ ∨ ∃ c : ℕ, 0 < c ∧
    ((H = {c * q, (c + 1) * q} ∧ p ∣ 2 * c + 1) ∨
     (H = {c * q, (c + 2) * q} ∧ p ∣ 2 * c + 2) ∨
     (H = {c * q, (c + 1) * q, (c + 2) * q} ∧ p ∣ 3 * c ^ 2 + 6 * c + 2))
  by_cases hempty : H = ∅
  · exact Or.inl hempty
  have hq : 0 < q := pow_pos hp.pos _
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hm.trans_le (mem_Icc.mp (hD hn)).1
  have hmem (n : ℕ) (hn : n ∈ H) : n ∈ D ∧ q ∣ n := mem_filter.mp hn
  have hcert (L : ℕ) (hL : ∀ n ∈ H, n / q ∣ L) :
      p ∣ ∑ n ∈ H, L / (n / q) := by
    simpa only [pow_zero, pow_one, zero_add, q, H] using
      Erdos287.cofactor_cut_congruence D p e L 0 hp he hpos hsum
        (fun n hn hnd => hL n (mem_filter.mpr ⟨hn, hnd⟩)) (by simp)
  have hdistinct {a b : ℕ} (hab : a < b) : a * q ≠ b * q :=
    (Nat.mul_lt_mul_of_pos_right hab hq).ne
  have htwo (a b : ℕ) (ha : 0 < a) (hab : a < b)
      (hpair : H = {a * q, b * q}) : p ∣ a + b := by
    have hb : 0 < b := ha.trans hab
    have hh := hcert (a * b) (by
      intro n hn
      rw [hpair, mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl
      · rw [Nat.mul_div_cancel _ hq]
        exact ⟨b, rfl⟩
      · rw [Nat.mul_div_cancel _ hq]
        exact ⟨a, mul_comm _ _⟩)
    rwa [hpair, sum_insert (by simpa using hdistinct hab), sum_singleton,
      Nat.mul_div_cancel _ hq, Nat.mul_div_cancel _ hq,
      Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel _ hb, add_comm] at hh
  obtain ⟨c, hc⟩ := (hmem (H.min' (nonempty_iff_ne_empty.mpr hempty))
    (H.min'_mem (nonempty_iff_ne_empty.mpr hempty))).2
  have hcH : c * q ∈ H := by
    rw [mul_comm, ← hc]
    exact H.min'_mem (nonempty_iff_ne_empty.mpr hempty)
  have hcpos : 0 < c := by
    have h := hpos _ (hmem _ hcH).1
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hcmin : m ≤ c * q := (mem_Icc.mp (hD (hmem _ hcH).1)).1
  have hsub : H ⊆ ({c * q, (c + 1) * q, (c + 2) * q} : Finset ℕ) := by
    intro n hn
    obtain ⟨a, ha⟩ := (hmem n hn).2
    have hal : c ≤ a := Nat.le_of_mul_le_mul_left (by
      rw [← hc, ← ha]
      exact H.min'_le _ hn) hq
    have haM : a * q ≤ M := by
      rw [mul_comm, ← ha]
      exact (mem_Icc.mp (hD (hmem n hn).1)).2
    have hau := hwindow c a hcmin haM
    have hcases : a = c ∨ a = c + 1 ∨ a = c + 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> simp [ha, mul_comm]
  have hc0 : c * q ≠ (c + 1) * q := hdistinct (by omega)
  have hc1 : c * q ≠ (c + 2) * q := hdistinct (by omega)
  have hc2 : (c + 1) * q ≠ (c + 2) * q := hdistinct (by omega)
  have hshape : H = ({c * q, (c + 1) * q, (c + 2) * q} : Finset ℕ).filter (· ∈ H) := by
    ext n
    exact mem_filter.trans (and_iff_right_of_imp (fun hn => hsub hn)) |>.symm
  refine Or.inr ⟨c, hcpos, ?_⟩
  by_cases h1 : (c + 1) * q ∈ H
  · by_cases h2 : (c + 2) * q ∈ H
    · have htriple : H = {c * q, (c + 1) * q, (c + 2) * q} := by
        simpa [filter_insert, filter_singleton, hcH, h1, h2] using hshape
      refine Or.inr (Or.inr ⟨htriple, ?_⟩)
      let L := c * (c + 1) * (c + 2)
      have hL₀ : L = ((c + 1) * (c + 2)) * c := by dsimp [L]; ring
      have hL₁ : L = (c * (c + 2)) * (c + 1) := by dsimp [L]; ring
      have hL₂ : L = (c * (c + 1)) * (c + 2) := rfl
      have hh := hcert L (by
        intro n hn
        rw [htriple, mem_insert, mem_insert, mem_singleton] at hn
        rcases hn with rfl | rfl | rfl <;> rw [Nat.mul_div_cancel _ hq]
        · exact ⟨(c + 1) * (c + 2), hL₀.trans (mul_comm _ _)⟩
        · exact ⟨c * (c + 2), hL₁.trans (mul_comm _ _)⟩
        · exact ⟨c * (c + 1), hL₂.trans (mul_comm _ _)⟩)
      rw [htriple, sum_insert (by simp [hc0, hc1]), sum_insert (by simp [hc2]),
        sum_singleton, Nat.mul_div_cancel _ hq, Nat.mul_div_cancel _ hq,
        Nat.mul_div_cancel _ hq] at hh
      rw [show L / c = (c + 1) * (c + 2) by rw [hL₀, Nat.mul_div_cancel _ hcpos],
        show L / (c + 1) = c * (c + 2) by rw [hL₁, Nat.mul_div_cancel _ (by omega)],
        show L / (c + 2) = c * (c + 1) by rw [hL₂, Nat.mul_div_cancel _ (by omega)]] at hh
      convert hh using 1
      ring
    · have hpair : H = {c * q, (c + 1) * q} := by
        simpa [filter_insert, filter_singleton, hcH, h1, h2] using hshape
      exact Or.inl ⟨hpair, by simpa only [two_mul, add_assoc] using htwo c (c + 1) hcpos (by omega) hpair⟩
  · by_cases h2 : (c + 2) * q ∈ H
    · have hpair : H = {c * q, (c + 2) * q} := by
        simpa [filter_insert, filter_singleton, hcH, h1, h2] using hshape
      exact Or.inr (Or.inl ⟨hpair, by
        simpa only [two_mul, add_assoc] using htwo c (c + 2) hcpos (by omega) hpair⟩)
    · have hsingle : H = {c * q} := by
        simpa [filter_insert, filter_singleton, hcH, h1, h2] using hshape
      have hh := hcert c (fun n hn => by
        rw [hsingle, mem_singleton] at hn
        simp only [hn, Nat.mul_div_cancel _ hq, dvd_refl])
      rw [hsingle, sum_singleton, Nat.mul_div_cancel _ hq, Nat.div_self hcpos] at hh
      exact (hp.not_dvd_one hh).elim

