-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_two_sided_mass_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:49:41.088585+00:00
-- url     : https://prove2.me/submissions/098a9256-5144-4621-a792-a7052c6b8ceb

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Two-sided exponential discount squeeze of the complete Stieltjes measure, valid for arbitrary diffuse, singular-continuous and countably atomic parts. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ∧
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by
  exact ⟨avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass
    q hq μ a b,
    avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
      q hq μ a b⟩
