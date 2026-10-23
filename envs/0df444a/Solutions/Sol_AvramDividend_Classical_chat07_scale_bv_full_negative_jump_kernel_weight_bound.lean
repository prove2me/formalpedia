-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_bv_full_negative_jump_kernel_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:45:47.248999+00:00
-- url     : https://prove2.me/submissions/3402c561-05a8-4b2f-8b8f-b321811e1230

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat07_scale_compensated_jump_small_linear_bound
import Theorems.Thm_AvramDividend_Classical_chat07_scale_uncompensated_jump_large_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

-- Combine compensated small jumps and uncompensated large jumps.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) *
        |W (x-r) - W x + (if r < 1 then r*deriv W x else 0)|) ≤
      min 1 r * max
        (θ * (X.ψ θ - q)⁻¹ +
          (∫ x in Ioi (0 : ℝ),
             Real.exp (-(θ*x)) * deriv W x))
        ((X.ψ θ - q)⁻¹) := by
  classical
  by_cases hsmall : r < 1
  · have hcap : min 1 r = r := min_eq_right hsmall.le
    simp only [if_pos hsmall, hcap]
    calc
      _ ≤ r * (θ * (X.ψ θ - q)⁻¹ +
          (∫ x in Ioi (0 : ℝ),
            Real.exp (-(θ*x)) * deriv W x)) :=
        chat07_scale_compensated_jump_small_linear_bound
          X q W hW θ r hθ hqθ hr
      _ ≤ r * max
          (θ * (X.ψ θ - q)⁻¹ +
            (∫ x in Ioi (0 : ℝ),
              Real.exp (-(θ*x)) * deriv W x))
          ((X.ψ θ - q)⁻¹) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hr.le
  · have hlarge : 1 ≤ r := le_of_not_gt hsmall
    have hcap : min 1 r = 1 := min_eq_left hlarge
    simp only [if_neg hsmall, add_zero, hcap, one_mul]
    have heq :
        (fun x : ℝ => Real.exp (-(θ*x)) * |W (x-r) - W x|) =
          (fun x : ℝ => Real.exp (-(θ*x)) * |W x - W (x-r)|) := by
      funext x
      rw [abs_sub_comm]
    rw [heq]
    exact (chat07_scale_uncompensated_jump_large_uniform_bound
      X q W hW θ hθ hqθ r hlarge).trans (le_max_right _ _)
