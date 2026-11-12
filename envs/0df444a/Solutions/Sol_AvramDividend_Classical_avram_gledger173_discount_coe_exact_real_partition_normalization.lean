-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger173_discount_coe_exact_real_partition_normalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:37:20.548298+00:00
-- url     : https://prove2.me/submissions/352eb9c7-b868-4364-a3a6-aba8b9c8d8af

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section
theorem solution
    (m k : ℕ) (ρ Δ : ℝ≥0) (q : ℝ) (W : ℕ → ℝ) :
    let E : ℝ≥0 → ℝ := fun u => Real.exp (-(q * (u : ℝ)))
    let s : ℕ → ℝ := fun i => (((i : ℝ≥0) * Δ : ℝ≥0) : ℝ)
    let t : ℝ := (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ)
    let r : ℝ := (ρ : ℝ) - t
    (∑ i ∈ Finset.range k,
      (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
        q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
    (E ρ - E ((k : ℝ≥0) * Δ) +
      (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k =
    (∑ i ∈ Finset.range k,
      (Real.exp (-(q * (s i + (Δ : ℝ)))) -
        Real.exp (-(q * s i)) +
        q * (Δ : ℝ) * Real.exp (-(q * s i))) * W i) +
    (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
      (if k < m then q * (Δ : ℝ) * Real.exp (-(q * t)) else 0)) * W k := by
  intro E s t r
  have hsum :
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) =
      (∑ i ∈ Finset.range k,
        (Real.exp (-(q * (s i + (Δ : ℝ)))) -
          Real.exp (-(q * s i)) +
          q * (Δ : ℝ) * Real.exp (-(q * s i))) * W i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [E, s, Nat.cast_add, add_mul, NNReal.coe_mul, NNReal.coe_add]
  have he : t + r = (ρ : ℝ) := by dsimp [r]; ring
  have hboundary :
      (E ρ - E ((k : ℝ≥0) * Δ) +
        (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k =
      (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
        (if k < m then q * (Δ : ℝ) * Real.exp (-(q * t)) else 0)) * W k := by
    simp only [E]
    rw [he]
  rw [hsum, hboundary]
