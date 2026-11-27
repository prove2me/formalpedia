-- Prove2me | solution 1 for Erdos287.dense_cofactor_reciprocal_split_iff_divisor_pair
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:44:09.446912+00:00
-- url     : https://prove2.me/submissions/7587eadc-b5cd-4c4f-8a84-dd15bf857421

import Mathlib

open Finset

set_option autoImplicit false

private theorem reciprocal_pair_iff (x y c : ℕ) (hc : 0 < c) (hx : c < x) (hy : c < y) :
    (1 : ℚ) / x + 1 / y = 1 / c ↔ (x - c) * (y - c) = c * c := by
  have hcQ : 0 < (c : ℚ) := by exact_mod_cast hc
  have hxQ : 0 < (x : ℚ) := by exact_mod_cast hc.trans hx
  have hyQ : 0 < (y : ℚ) := by exact_mod_cast hc.trans hy
  constructor
  · intro h
    field_simp at h
    have hq : ((x - c : ℕ) : ℚ) * ((y - c : ℕ) : ℚ) = (c : ℚ) * c := by
      rw [Nat.cast_sub hx.le, Nat.cast_sub hy.le]
      linear_combination -h
    exact_mod_cast hq
  · intro h
    have hq : ((x - c : ℕ) : ℚ) * ((y - c : ℕ) : ℚ) = (c : ℚ) * c := by exact_mod_cast h
    rw [Nat.cast_sub hx.le, Nat.cast_sub hy.le] at hq
    field_simp
    linear_combination -hq

/-- Below three times the first cofactor, the higher-cofactor reciprocal
decompositions of the first term are precisely the two-term divisor splits. -/
theorem solution (A : Finset ℕ) (c B : ℕ) (hc : 0 < c) (hB : B < 3 * c)
    (hA : A ⊆ Finset.Ioc c B) :
    (∑ a ∈ A, (1 : ℚ) / a = (1 : ℚ) / c) ↔
      ∃ d, 0 < d ∧ d < c ∧ d ∣ c * c ∧ c + c * c / d ≤ B ∧
        A = {c + d, c + c * c / d} := by
  classical
  have hcQ : 0 < (c : ℚ) := by exact_mod_cast hc
  constructor
  · intro hsum
    have hne : A.Nonempty := by
      by_contra! h
      rw [h, sum_empty] at hsum
      exact (one_div_pos.mpr hcQ).ne' hsum.symm
    obtain ⟨a, ha⟩ := hne
    have hBpos : 0 < B := (hc.trans (mem_Ioc.mp (hA ha)).1).trans_le (mem_Ioc.mp (hA ha)).2
    have hBQ : 0 < (B : ℚ) := by exact_mod_cast hBpos
    have hUpper : ((A.card : ℕ) : ℚ) / B ≤ (1 : ℚ) / c := by
      rw [← hsum]
      calc
        _ = ∑ _ ∈ A, (1 : ℚ) / B := by simp [div_eq_mul_inv]
        _ ≤ _ := by
          apply sum_le_sum
          intro x hx
          exact one_div_le_one_div_of_le (by exact_mod_cast hc.trans (mem_Ioc.mp (hA hx)).1)
            (by exact_mod_cast (mem_Ioc.mp (hA hx)).2)
    have hCard : A.card < 3 := by
      by_contra! h
      have h3 : (3 : ℚ) / B ≤ (1 : ℚ) / c :=
        (div_le_div_of_nonneg_right (by exact_mod_cast h) hBQ.le).trans hUpper
      have h3' := (div_le_div_iff₀ hBQ hcQ).mp h3
      have hb' : (B : ℚ) < 3 * c := by exact_mod_cast hB
      linarith
    have hCard1 : A.card ≠ 1 := by
      intro h
      obtain ⟨x, rfl⟩ := card_eq_one.mp h
      have hcx : (c : ℚ) < x := by exact_mod_cast (mem_Ioc.mp (hA (mem_singleton_self x))).1
      exact (one_div_lt_one_div_of_lt hcQ hcx).ne (by simpa only [sum_singleton] using hsum)
    have hCard2 : A.card = 2 := by have := card_pos.mpr ⟨a, ha⟩; omega
    obtain ⟨x, y, hxy, hEq⟩ := card_eq_two.mp hCard2
    have ordered (a b : ℕ) (hab : a < b) (hPair : A = {a, b}) :
        ∃ d, 0 < d ∧ d < c ∧ d ∣ c * c ∧ c + c * c / d ≤ B ∧
          A = {c + d, c + c * c / d} := by
      have haA : a ∈ A := by rw [hPair]; simp
      have hbA : b ∈ A := by rw [hPair]; simp
      have ha := (mem_Ioc.mp (hA haA)).1
      have hb := (mem_Ioc.mp (hA hbA)).1
      have hProd : (a - c) * (b - c) = c * c := (reciprocal_pair_iff a b c hc ha hb).mp
        (by simpa [hPair, sum_insert, hab.ne] using hsum)
      let d := a - c
      let e := b - c
      have hd : 0 < d := by dsimp [d]; omega
      have hde : d < e := by dsimp [d, e]; omega
      have hDC : d < c := by
        by_contra! h
        have hce := h.trans_lt hde
        have h₁ := Nat.mul_le_mul_right c h
        have h₂ := Nat.mul_lt_mul_of_pos_left hce hd
        exact (h₁.trans_lt h₂).ne hProd.symm
      have hquot : c * c / d = e := by rw [← hProd]; exact Nat.mul_div_cancel_left e hd
      have ha' : c + d = a := by dsimp [d]; omega
      have hb' : c + e = b := by dsimp [e]; omega
      refine ⟨d, hd, hDC, ⟨e, hProd.symm⟩, ?_, ?_⟩
      · rw [hquot, hb']
        exact (mem_Ioc.mp (hA hbA)).2
      · rw [hquot, ha', hb', hPair]
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ordered x y h hEq
    · exact ordered y x h (hEq.trans (pair_comm _ _))
  · rintro ⟨d, hd, hdc, hdiv, _, rfl⟩
    let e := c * c / d
    have hProd : e * d = c * c := Nat.div_mul_cancel hdiv
    have hce : c < e := by
      by_contra! h
      have h₁ := Nat.mul_le_mul_right d h
      have h₂ := Nat.mul_lt_mul_of_pos_left hdc hc
      exact (h₁.trans_lt h₂).ne hProd
    have hne : c + d ∉ ({c + e} : Finset ℕ) := by simp only [mem_singleton]; omega
    change (∑ x ∈ ({c + d, c + e} : Finset ℕ), (1 : ℚ) / x) = _
    rw [sum_insert hne, sum_singleton]
    apply (reciprocal_pair_iff _ _ c hc (by omega) (by omega)).mpr
    simpa only [Nat.add_sub_cancel_left, mul_comm d e] using hProd

