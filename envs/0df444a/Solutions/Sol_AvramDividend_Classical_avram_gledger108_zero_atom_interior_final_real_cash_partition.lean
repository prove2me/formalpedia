-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger108_zero_atom_interior_final_real_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:26:38.543082+00:00
-- url     : https://prove2.me/submissions/ca684ea9-b583-4a56-bfdd-cc3d407cf5e5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_gledger95_zero_atom_interior_final_cash_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Finite strict stopped cash admits the same chronological partition
    after converting its nonnegative integrals to real values. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hfinite : (∫⁻ s in S ∩ Iio ρ, f s ∂μ) < ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal =
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ).toReal := by
  let a : ℝ≥0∞ := ∫⁻ s in S ∩ {0}, f s ∂μ
  let cell : ℕ → ℝ≥0∞ := fun i =>
    ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ
  let b : ℝ≥0∞ := ∑ i ∈ Finset.range k, cell i
  let c : ℝ≥0∞ := ∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ
  have hpart : (∫⁻ s in S ∩ Iio ρ, f s ∂μ) = a + b + c := by
    simpa only [a, b, c, cell] using
      (avram_gledger95_zero_atom_interior_final_cash_partition
        μ f S hS hSnonneg v hv hv0 k ρ hvk hstop)
  have hparts : a + b + c < ⊤ := by
    rw [← hpart]
    exact hfinite
  have ha : a < ⊤ := by
    apply lt_of_le_of_lt _ hparts
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hb : b < ⊤ := by
    apply lt_of_le_of_lt _ hparts
    exact (le_add_of_nonneg_left (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hc : c < ⊤ := by
    apply lt_of_le_of_lt _ hparts
    exact le_add_of_nonneg_left (by positivity)
  have hab : a + b < ⊤ :=
    lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hparts
  have hcell : ∀ i ∈ Finset.range k, cell i ≠ ⊤ := by
    intro i hi
    have hle : cell i ≤ b := by
      dsimp [b]
      exact Finset.single_le_sum (fun j hj => bot_le) hi
    exact ne_of_lt (lt_of_le_of_lt hle hb)
  have hsum : b.toReal =
      ∑ i ∈ Finset.range k, (cell i).toReal := by
    simpa only [b] using
      (ENNReal.toReal_sum (s := Finset.range k) (f := cell) hcell)
  calc
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal = (a + b + c).toReal :=
      congrArg ENNReal.toReal hpart
    _ = a.toReal + b.toReal + c.toReal := by
      rw [ENNReal.toReal_add (ne_of_lt hab) (ne_of_lt hc)]
      rw [ENNReal.toReal_add (ne_of_lt ha) (ne_of_lt hb)]
    _ = _ := by simpa only [a, c, cell, hsum]
