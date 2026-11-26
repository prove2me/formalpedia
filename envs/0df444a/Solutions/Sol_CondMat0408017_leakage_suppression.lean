-- Prove2me | solution 1 for CondMat0408017.leakage_suppression
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:34:48.278918+00:00
-- url     : https://prove2.me/submissions/d70bfca8-5246-4bbb-a854-ef9c6c5e3e06

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (k1 Δk : ℝ) (hk1 : 0 < k1) (hΔk : 0 ≤ Δk) :
    ∀ (j : ℕ) (Q : Fin j → ℝ), (∀ i, Q i ∈ westODonnellSupport k1 Δk) →
      (∃ s : ℤ, |s| ≤ (j : ℤ) ∧ Even (s + (j : ℤ)) ∧
        |k1 + ∑ i, Q i - (2 * (s : ℝ) + 1) * k1| ≤ (j : ℝ) * Δk) ∧
      ∀ (n : ℕ) (wv : ℝ), 0 ≤ wv → j ≤ n → Δk < (k1 - wv) / n → wv < |k1 + ∑ i, Q i| := by
  intro j Q hQ
  let ε : Fin j → ℤ := fun i => if 0 ≤ Q i then 1 else -1
  let s : ℤ := ∑ i : Fin j, ε i
  have hpart1 : |s| ≤ (j : ℤ) ∧ Even (s + (j : ℤ)) ∧
      |k1 + ∑ i, Q i - (2 * (s : ℝ) + 1) * k1| ≤ (j : ℝ) * Δk := by
    refine ⟨?_, ?_, ?_⟩
    · calc |s| ≤ ∑ i : Fin j, |ε i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ _i : Fin j, (1 : ℤ) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [ε]; split_ifs <;> norm_num
        _ = (j : ℤ) := by simp
    · have hsum : s + (j : ℤ) = ∑ i : Fin j, (ε i + 1) := by
        simp [s, Finset.sum_add_distrib]
      rw [hsum]
      have h2 : ∑ i : Fin j, (ε i + 1) = 2 * ∑ i : Fin j, (if 0 ≤ Q i then (1 : ℤ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [ε]; split_ifs <;> norm_num
      rw [h2]
      exact even_two_mul _
    · have hrew : k1 + ∑ i, Q i - (2 * (s : ℝ) + 1) * k1 =
          ∑ i : Fin j, (Q i - 2 * (ε i : ℝ) * k1) := by
        have hsR : (s : ℝ) = ∑ i : Fin j, (ε i : ℝ) := by simp [s]
        rw [hsR, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
      rw [hrew]
      calc |∑ i : Fin j, (Q i - 2 * (ε i : ℝ) * k1)|
          ≤ ∑ i : Fin j, |Q i - 2 * (ε i : ℝ) * k1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin j, Δk := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            obtain ⟨hlo, hhi⟩ := hQ i
            simp only [ε]
            split_ifs with h0
            · rw [abs_of_nonneg h0] at hlo hhi
              simp only [Int.cast_one, mul_one]
              rw [abs_le]
              constructor <;> linarith
            · push Not at h0
              rw [abs_of_neg h0] at hlo hhi
              simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
              rw [abs_le]
              constructor <;> linarith
        _ = (j : ℝ) * Δk := by simp
  refine ⟨⟨s, hpart1⟩, ?_⟩
  intro n wv hwv hjn hΔlt
  have hn_pos : (0 : ℝ) < n := by
    by_contra hle
    push Not at hle
    have hn0 : (n : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg n)
    rw [hn0, div_zero] at hΔlt
    linarith
  have hjk : (j : ℝ) * Δk < k1 - wv := by
    have hjle : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
    have h1 : (j : ℝ) * Δk ≤ (n : ℝ) * Δk := mul_le_mul_of_nonneg_right hjle hΔk
    have h2 : (n : ℝ) * Δk < k1 - wv := by
      rwa [lt_div_iff₀ hn_pos, mul_comm] at hΔlt
    linarith
  have hodd : (1 : ℝ) ≤ |(2 * (s : ℝ) + 1)| := by
    have hint : (1 : ℤ) ≤ |2 * s + 1| := by
      rcases le_or_gt 0 (2 * s + 1) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    have hcast : ((1 : ℤ) : ℝ) ≤ ((|2 * s + 1| : ℤ) : ℝ) := Int.cast_le.mpr hint
    simpa [Int.cast_abs] using hcast
  have hcenter : k1 ≤ |(2 * (s : ℝ) + 1) * k1| := by
    rw [abs_mul, abs_of_pos hk1]
    nlinarith
  have htri : |(2 * (s : ℝ) + 1) * k1| - |k1 + ∑ i, Q i| ≤
      |k1 + ∑ i, Q i - (2 * (s : ℝ) + 1) * k1| := by
    have := abs_sub_abs_le_abs_sub ((2 * (s : ℝ) + 1) * k1) (k1 + ∑ i, Q i)
    rw [abs_sub_comm] at this
    exact this
  linarith [hpart1.2.2]
