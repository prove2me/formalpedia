-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger168_clipped_discount_counterterm_sum_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:36.188849+00:00
-- url     : https://prove2.me/submissions/ea31622d-d641-403d-8373-9e174ccf30f2

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
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ then q * (Δ : ℝ) * E s * W i else 0) =
      (∑ i ∈ Finset.range k,
        q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ) * W i) +
      (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) * W k else 0) := by
  intro Δ v E
  let f : ℕ → ℝ := fun i => q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ) * W i
  let g : ℕ → ℝ := fun i =>
    if (i : ℝ≥0) * Δ < ρ then f i else 0
  change (∑ i ∈ Finset.range m, g i) =
    (∑ i ∈ Finset.range k, f i) + (if k < m then f k else 0)
  have hfirst : (∑ i ∈ Finset.range k, g i) =
      (∑ i ∈ Finset.range k, f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have his : (i : ℝ≥0) * Δ < ρ := hlo i (Nat.le_of_lt (Finset.mem_range.mp hi))
    exact if_pos his
  have hzero (i : ℕ) (hi : k < i) : g i = 0 := by
    have hs : ¬ (i : ℝ≥0) * Δ < ρ := not_lt.mpr (hhi i hi)
    exact if_neg hs
  have htail : (∑ i ∈ Finset.range (m - k), g (k + i)) =
      (if k < m then f k else 0) := by
    by_cases hkm : k < m
    · have hpos : 0 < m - k := Nat.sub_pos_of_lt hkm
      cases heq : m - k with
      | zero => omega
      | succ r =>
        have hz : (∑ i ∈ Finset.range r, g (k + (i + 1))) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact hzero _ (by omega)
        have hfk : g k = f k := if_pos (hlo k le_rfl)
        simp only [heq, Finset.sum_range_succ']
        simp [hz, hfk, hkm, Nat.add_assoc]
    · have hmk : m = k := by omega
      have hz : m - k = 0 := by omega
      simp [hz, hkm]
  calc
    (∑ i ∈ Finset.range m, g i) =
        (∑ i ∈ Finset.range (k + (m - k)), g i) := by
          have heq : k + (m - k) = m := by omega
          rw [heq]
    _ = (∑ i ∈ Finset.range k, g i) +
        (∑ i ∈ Finset.range (m - k), g (k + i)) := by
          rw [Finset.sum_range_add]
    _ = (∑ i ∈ Finset.range k, f i) +
        (if k < m then f k else 0) := by rw [hfirst, htail]
