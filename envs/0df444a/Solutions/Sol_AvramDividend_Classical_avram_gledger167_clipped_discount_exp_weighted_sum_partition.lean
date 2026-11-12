-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger167_clipped_discount_exp_weighted_sum_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:08:34.53748+00:00
-- url     : https://prove2.me/submissions/cfd4e118-df2c-4048-917b-622a1c37ae49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (q : ℝ) (W : ℕ → ℝ) (k : ℕ)
    (hk : k ≤ m)
    (hlo : ∀ i : ℕ, i ≤ k →
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ)
    (hhi : ∀ i : ℕ, k < i →
      ρ ≤ ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    (∑ i ∈ Finset.range (m + 1), (E (v (i + 1)) - E (v i)) * W i) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ)) * W i) +
        (E ρ - E ((k : ℝ≥0) * Δ)) * W k := by
  intro Δ v E
  let f : ℕ → ℝ := fun i => (E (v (i + 1)) - E (v i)) * W i
  let g : ℕ → ℝ := fun i =>
    (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ)) * W i
  change (∑ i ∈ Finset.range (m + 1), f i) =
    (∑ i ∈ Finset.range k, g i) +
    (E ρ - E ((k : ℝ≥0) * Δ)) * W k
  have hfirst : (∑ i ∈ Finset.range k, f i) =
      (∑ i ∈ Finset.range k, g i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hs0 : (i : ℝ≥0) * Δ < ρ := hlo i hik.le
    have hs1 : (((i + 1 : ℕ) : ℝ≥0) * Δ) < ρ :=
      hlo (i + 1) (Nat.succ_le_iff.mpr hik)
    simpa only [f, g, v, min_eq_left hs0.le, min_eq_left hs1.le]
  have hkterm : f k = (E ρ - E ((k : ℝ≥0) * Δ)) * W k := by
    have hs0 : (k : ℝ≥0) * Δ < ρ := hlo k le_rfl
    have hs1 : ρ ≤ (((k + 1 : ℕ) : ℝ≥0) * Δ) :=
      hhi (k + 1) (Nat.lt_succ_self k)
    simpa only [f, v, min_eq_left hs0.le, min_eq_right hs1]
  have hzero (i : ℕ) (hi : k < i) : f i = 0 := by
    have hs0 : ρ ≤ ((i : ℝ≥0) * Δ) := hhi i hi
    have hs1 : ρ ≤ (((i + 1 : ℕ) : ℝ≥0) * Δ) :=
      hhi (i + 1) (by omega)
    simpa only [f, v, min_eq_right hs0, min_eq_right hs1, sub_self, zero_mul]
  have htail : (∑ i ∈ Finset.range (m - k),
      f ((k + 1) + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hzero _ (by omega)
  calc
    (∑ i ∈ Finset.range (m + 1), f i) =
      (∑ i ∈ Finset.range ((k + 1) + (m - k)), f i) := by
        have heq : (k + 1) + (m - k) = m + 1 := by omega
        rw [heq]
    _ = (∑ i ∈ Finset.range (k + 1), f i) +
        (∑ i ∈ Finset.range (m - k), f ((k + 1) + i)) := by
          rw [Finset.sum_range_add]
    _ = (∑ i ∈ Finset.range k, g i) +
        (E ρ - E ((k : ℝ≥0) * Δ)) * W k := by
          rw [htail, add_zero, Finset.sum_range_succ, hfirst, hkterm]
