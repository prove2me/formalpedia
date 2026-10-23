-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_compensated_jump_small_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:36:13.183915+00:00
-- url     : https://prove2.me/submissions/18442789-9dce-413f-8524-1f8f21332922

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_compensated_jump_l1_bound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Linear small-jump domination of the weighted compensated scale kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |W (x-r) - W x + r*deriv W x|) ≤
      r * (θ * (X.ψ θ - q)⁻¹ +
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x)) * deriv W x)) := by
  have hden : 0 ≤ (X.ψ θ - q)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hqθ))
  have hmin : min 1 (θ*r) ≤ θ*r := min_le_right _ _
  have hmul :
      min 1 (θ*r) * (X.ψ θ-q)⁻¹ ≤
      (θ*r) * (X.ψ θ-q)⁻¹ :=
    mul_le_mul_of_nonneg_right hmin hden
  calc
    _ ≤ min 1 (θ*r) * (X.ψ θ-q)⁻¹ +
        r * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*deriv W x) :=
      chat07_scale_weighted_compensated_jump_l1_bound
        X q W hW θ r hθ hqθ hr
    _ ≤ (θ*r) * (X.ψ θ-q)⁻¹ +
        r * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*deriv W x) :=
      add_le_add hmul le_rfl
    _ = r * (θ * (X.ψ θ-q)⁻¹ +
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*deriv W x)) := by ring
