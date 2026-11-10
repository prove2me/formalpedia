-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T20:37:41.552496+00:00
-- url     : https://prove2.me/submissions/c6ce8868-c81b-491b-b8ac-e55b0f8aff56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    (q rate w0 cash s t : ℝ)
    (hq : 0 < q) (hrate : 0 ≤ rate) (hw0 : 0 ≤ w0)
    (hst : s ≤ t)
    (hCash : cash ≤ (q + rate) * w0 *
      ((Real.exp (-(q * s)) - Real.exp (-(q * t))) / q)) :
    cash + Real.exp (-(q * t)) * w0 -
      Real.exp (-(q * s)) * w0 ≤
      rate * w0 * Real.exp (-(q * s)) * (t - s) := by
  let d : ℝ := Real.exp (-(q * s)) - Real.exp (-(q * t))
  have hexp : Real.exp (-(q * t)) =
      Real.exp (-(q * s)) * Real.exp (-(q * (t - s))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiff : d ≤ q * Real.exp (-(q * s)) * (t - s) := by
    have hlin : 1 - Real.exp (-(q * (t - s))) ≤ q * (t - s) := by
      linarith [Real.add_one_le_exp (-(q * (t - s)))]
    have hscaled := mul_le_mul_of_nonneg_left hlin
      (le_of_lt (Real.exp_pos (-(q * s))))
    dsimp [d]
    rw [hexp]
    nlinarith [hscaled]
  have hdiv : d / q ≤ Real.exp (-(q * s)) * (t - s) := by
    apply (div_le_iff₀ hq).2
    nlinarith [hdiff]
  have hnonneg : 0 ≤ rate * w0 := mul_nonneg hrate hw0
  have hmul := mul_le_mul_of_nonneg_left hdiv hnonneg
  calc
    cash + Real.exp (-(q * t)) * w0 - Real.exp (-(q * s)) * w0
        ≤ (q + rate) * w0 * (d / q) +
          Real.exp (-(q * t)) * w0 -
          Real.exp (-(q * s)) * w0 := by
            dsimp [d] at hCash ⊢
            linarith
    _ = rate * w0 * (d / q) := by
      dsimp [d]
      field_simp [ne_of_gt hq]
      ring
    _ ≤ rate * w0 * Real.exp (-(q * s)) * (t - s) := by
      nlinarith [hmul]
