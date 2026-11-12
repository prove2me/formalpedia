-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger174_clipped_discount_compact_weight_replacement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:51:10.611947+00:00
-- url     : https://prove2.me/submissions/b2458a50-fde6-4997-9444-542e3a6521a0

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
    (n m : ℕ) (ρ : ℝ≥0) (q : ℝ) (w H : ℝ → ℝ)
    (Y : ℝ≥0 → ℝ)
    (hHw : ∀ t : ℝ≥0, t < ρ → H (Y t) = w (Y t)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    (∑ i ∈ Finset.range (m + 1),
      (E (v (i + 1)) - E (v i)) * H (Y (v i))) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * H (Y s) else 0) =
    (∑ i ∈ Finset.range (m + 1),
      (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * w (Y s) else 0) := by
  intro Δ v E
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : (i : ℝ≥0) * Δ < ρ
    · have hv : v i < ρ := by
        simpa only [v, min_eq_left hs.le] using hs
      rw [hHw (v i) hv]
    · have hsmall : ρ ≤ (i : ℝ≥0) * Δ := le_of_not_gt hs
      have hbig : ρ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ :=
        hsmall.trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_succ i) Δ.property)
      simp only [v, min_eq_right hsmall, min_eq_right hbig, sub_self, zero_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    change (if s < ρ then q * (Δ : ℝ) * E s * H (Y s) else 0) =
      (if s < ρ then q * (Δ : ℝ) * E s * w (Y s) else 0)
    by_cases hs : s < ρ
    · simp only [if_pos hs, hHw s hs]
    · simp only [if_neg hs]
