-- Prove2me | solution 2 for DynEdgeOrient.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:12:52.40285+00:00
-- url     : https://prove2.me/submissions/f6f0e6ab-0c3a-4e93-bbb9-cdc105872d0d

import Mathlib

theorem solution (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hAdef
  set B := ∑ i, b i with hBdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases hA0.lt_or_eq with hA | hA
  · have hB : 0 < B := by
      rcases hB0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hball : ∀ i ∈ Finset.univ, b i = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hb i).mp h.symm
        have : A = 0 := by
          rw [hAdef]
          exact Finset.sum_eq_zero fun i hi => hab i (hball i hi)
        linarith
    have hterm : ∀ i, a i - b i * (A / B) ≤ a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
      intro i
      rcases (ha i).lt_or_eq with hpos | hzero
      · have hbpos : 0 < b i := lt_of_le_of_ne (hb i) (fun h => hpos.ne' (hab i h.symm))
        have hy : 0 < (a i / b i) / (A / B) := by positivity
        have h := Real.one_sub_inv_le_log_of_pos hy
        rw [Real.log_div (by positivity) (by positivity)] at h
        have h2 := mul_le_mul_of_nonneg_left h (ha i)
        have e : a i * (1 - ((a i / b i) / (A / B))⁻¹) = a i - b i * (A / B) := by
          field_simp
        linarith
      · rw [← hzero]
        simp only [zero_sub, zero_mul, sub_zero]
        have : 0 ≤ b i * (A / B) := by have := hb i; positivity
        linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← hAdef, ← hBdef] at hsum
    have e : A - B * (A / B) = 0 := by field_simp; ring
    linarith
  · rw [← hA, zero_mul]
    have hall : ∀ i ∈ Finset.univ, a i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ha i).mp hA.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hall i hi, zero_mul]]
