-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_le_min
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:16:04.957697+00:00
-- url     : https://prove2.me/submissions/d1dffda3-a78d-442c-8ffe-8d3470654c94

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_exact
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! First-order small-jump control and uniform large-jump control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * |W x - W (x - r)|) ≤
      min 1 (θ * r) * (X.ψ θ - q)⁻¹ := by
  have h1 : 1 - Real.exp (-(θ * r)) ≤ (1 : ℝ) := by
    linarith [Real.exp_nonneg (-(θ * r))]
  have h2 : 1 - Real.exp (-(θ * r)) ≤ θ * r := by
    linarith [Real.one_sub_le_exp_neg (θ * r)]
  have hInv : 0 ≤ (X.ψ θ - q)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hqθ))
  rw [chat07_scale_shift_weighted_abs_integral_exact X q W hW θ hθ hqθ r hr]
  exact mul_le_mul_of_nonneg_right (le_min h1 h2) hInv
