-- Prove2me | solution 1 for AvramDividend.Classical.psi_quadratic_lower_from_compensated_negative_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:12:47.616461+00:00
-- url     : https://prove2.me/submissions/596c63c0-abe5-473d-b0fb-3866a5a43404

import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The compensated small-negative-jump term is nonnegative, leaving a quadratic exponent bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) ≤ X.ψ θ := by
  have hbase :=
    psi_lower_bound_by_compensated_small_jumps X θ hθ
      (levy_large_negative_jump_unit_integrable X)
  have hjump : 0 ≤
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) := by
    apply integral_nonneg
    intro y
    change 0 ≤ Real.exp (θ * y) - 1 - θ * y
    have h_exp := Real.add_one_le_exp (θ * y)
    linarith
  linarith
