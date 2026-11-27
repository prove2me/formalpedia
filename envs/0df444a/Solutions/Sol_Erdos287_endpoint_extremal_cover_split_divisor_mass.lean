-- Prove2me | solution 1 for Erdos287.endpoint_extremal_cover_split_divisor_mass
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:23:19.651827+00:00
-- url     : https://prove2.me/submissions/448650b7-03c7-407e-a971-9ed6145cd7de

import Mathlib
import Theorems.Thm_Erdos287_endpoint_extremal_cover_trimmed_mass_obstruction

open Finset

set_option autoImplicit false

/-- Each feasible two-term split of the least denominator has a selected
output. Divisors below the least denominator give disjoint output pairs. -/
theorem solution (D B : Finset ℕ) (m M : ℕ) (hm : 1 < m) (hmD : m ∈ D)
    (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hextreme : ∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m))
    (hB : ∀ d ∈ B, 0 < d ∧ d < m ∧ d ∣ m * m ∧ m + m * m / d ≤ M) :
    let S := D.filter (fun n => ∃ d ∈ B, n = m + d ∨ n = m + m * m / d)
    B.card ≤ S.card ∧
      (∑ d ∈ B, (1 : ℚ) / ((m + m * m / d : ℕ) : ℚ)) ≤ ∑ n ∈ S, (1 : ℚ) / n := by
  classical
  intro S
  let q (d : ℕ) := m * m / d
  have hp (d : ℕ) (h : d ∈ B) : q d * d = m * m := Nat.div_mul_cancel (hB d h).2.2.1
  have hq (d : ℕ) (h : d ∈ B) : m < q d := by
    by_contra! hle
    have h₁ := Nat.mul_le_mul_right d hle
    have h₂ := Nat.mul_lt_mul_of_pos_left (hB d h).2.1 (show 0 < m by omega)
    exact (h₁.trans_lt h₂).ne (hp d h)
  have hR : D.filter (fun x => x < m + 1 ∨ M < x) = {m} := by
    ext x
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hx, hr⟩
      have hi := mem_Icc.mp (hD hx)
      omega
    · rintro rfl
      exact ⟨hmD, Or.inl (by omega)⟩
  have select (d : ℕ) (h : d ∈ B) : m + d ∈ D ∨ m + q d ∈ D := by
    by_contra! hh
    let A : Finset ℕ := {m + d, m + q d}
    have hd := (hB d h).1
    have hdm := (hB d h).2.1
    have hmd := hq d h
    have hM : m + q d ≤ M := (hB d h).2.2.2
    have hA : A ⊆ Icc (m + 1) M := by
      intro x hx
      simp only [A, mem_insert, mem_singleton] at hx
      exact mem_Icc.mpr (by omega)
    have hAD : Disjoint A D := disjoint_left.mpr (fun {x} hx hxd => by
      simp only [A, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hh.1 hxd
      · exact hh.2 hxd)
    have hmass : ∑ n ∈ A, (1 : ℚ) / n = (1 : ℚ) / m := by
      have hne : m + d ∉ ({m + q d} : Finset ℕ) := by simp only [mem_singleton]; omega
      simp only [A, sum_insert hne, sum_singleton, Nat.cast_add]
      have hmQ : 0 < (m : ℚ) := by exact_mod_cast (show 0 < m by omega)
      have hdQ : 0 < (d : ℚ) := by exact_mod_cast hd
      have hqQ : 0 < ((q d : ℕ) : ℚ) := by exact_mod_cast (show 0 < q d by omega)
      have hprod : ((q d : ℕ) : ℚ) * d = (m : ℚ) * m := by exact_mod_cast hp d h
      field_simp
      linear_combination -hprod
    have hblock := Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction D A m M (m + 1) M
      hm hcover hsum hextreme (by omega) le_rfl (Or.inl (by omega)) hA hAD
    rw [hR, sum_singleton] at hblock
    exact hblock hmass
  let w (d : ℕ) := if m + d ∈ D then m + d else m + q d
  have hwin (d : ℕ) (hd : d ∈ B) : w d ∈ D := by
    by_cases h : m + d ∈ D
    · simp [w, h]
    · simpa [w, h] using (select d hd).resolve_left h
  have hchoice (d : ℕ) : w d = m + d ∨ w d = m + q d := by
    by_cases h : m + d ∈ D <;> simp [w, h]
  have hinj : Set.InjOn w ↑B := by
    intro d hd e he hw
    have hd' : d ∈ B := hd
    have he' : e ∈ B := he
    have hdlo := (hB d hd').2.1
    have helo := (hB e he').2.1
    have hdhi := hq d hd'
    have hehi := hq e he'
    rcases hchoice d with hdl | hdu <;> rcases hchoice e with hel | heu
    · omega
    · omega
    · omega
    · have hqeq : q d = q e := by omega
      exact Nat.eq_of_mul_eq_mul_left (show 0 < q d by omega) (by rw [hp d hd', hqeq, hp e he'])
  have hsub : B.image w ⊆ S := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hn
    exact mem_filter.mpr ⟨hwin d hd, d, hd, hchoice d⟩
  constructor
  · rw [← card_image_of_injOn hinj]
    exact card_le_card hsub
  · calc
      (∑ d ∈ B, (1 : ℚ) / ((m + m * m / d : ℕ) : ℚ)) ≤
          ∑ d ∈ B, (1 : ℚ) / w d := by
        apply sum_le_sum
        intro d hd
        have hdl := (hB d hd).2.1
        have hqu := hq d hd
        have h₀ : 0 < w d := by rcases hchoice d with h | h <;> omega
        have h₁ : w d ≤ m + q d := by rcases hchoice d with h | h <;> omega
        exact one_div_le_one_div_of_le (by exact_mod_cast h₀) (by exact_mod_cast h₁)
      _ = ∑ n ∈ B.image w, (1 : ℚ) / n := by rw [sum_image hinj]
      _ ≤ ∑ n ∈ S, (1 : ℚ) / n := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

