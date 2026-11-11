-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger33_strict_discounted_open_cell_upper_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:42:13.755202+00:00
-- url     : https://prove2.me/submissions/860181a2-a136-48ab-9926-9771af73c002

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_discounted_right_endpoint_cell_upper_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Restrict below the terminal endpoint before applying the proved
    right-closed discount estimate, so no final dividend atom enters. -/
theorem solution (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioo a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioo a b) := by
  let ν : Measure ℝ := μ.restrict (Iio b)
  have hInterval : Ioc a b ∩ Iio b = Ioo a b := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨⟨has, _⟩, hsb⟩
      exact ⟨has, hsb⟩
    · rintro ⟨has, hsb⟩
      exact ⟨⟨has, le_of_lt hsb⟩, hsb⟩
  have hRestr : ν.restrict (Ioc a b) = μ.restrict (Ioo a b) := by
    dsimp [ν]
    rw [Measure.restrict_restrict measurableSet_Ioc, hInterval]
  have hMass : ν (Ioc a b) = μ (Ioo a b) := by
    dsimp [ν]
    rw [Measure.restrict_apply measurableSet_Ioc, hInterval]
  have hBudget := avram_wave6_08_discounted_right_endpoint_cell_upper_error
    q hq ν a b ha hab
  simpa only [hRestr, hMass] using hBudget
