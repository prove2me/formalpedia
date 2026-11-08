-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_discount_loss_total_at_most_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:38:14.04141+00:00
-- url     : https://prove2.me/submissions/a53f062d-7434-4bc4-b64e-c5509f6a01fc

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical-grid discount losses telescope and have total mass at most one. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m : ℕ) (h0 : u 0 = 0) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) =
      1 - Real.exp (-(q * (u (m + 1) : ℝ))) ∧
    0 ≤ (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) ∧
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) ≤ 1 := by
  have htel_aux : ∀ k : ℕ,
      (∑ i ∈ Finset.range k,
        (Real.exp (-(q * (u i : ℝ))) -
          Real.exp (-(q * (u (i + 1) : ℝ))))) =
        Real.exp (-(q * (u 0 : ℝ))) -
          Real.exp (-(q * (u k : ℝ))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have htel := htel_aux (m + 1)
  have hzero : Real.exp (-(q * (u 0 : ℝ))) = 1 := by simp [h0]
  rw [hzero] at htel
  refine ⟨htel, ?_⟩
  rw [htel]
  have hnonneg : 0 ≤ (u (m + 1) : ℝ) := NNReal.coe_nonneg _
  have harg : -(q * (u (m + 1) : ℝ)) ≤ 0 := by
    nlinarith [mul_nonneg hq hnonneg]
  have hexp_le_one :
      Real.exp (-(q * (u (m + 1) : ℝ))) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr harg)
  have hexp_pos : 0 < Real.exp (-(q * (u (m + 1) : ℝ))) :=
    Real.exp_pos _
  constructor <;> linarith
