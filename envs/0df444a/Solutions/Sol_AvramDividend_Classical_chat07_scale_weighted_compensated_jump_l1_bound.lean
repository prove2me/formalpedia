-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_weighted_compensated_jump_l1_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:24:53.451101+00:00
-- url     : https://prove2.me/submissions/24db44e0-e820-4a18-876f-d9e490fc23e6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_negative_jump_integrableOn
import Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_jump_integral_triangle
import Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_le_min
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-! BV compensated negative jump: fixed-jump first-order weighted L1 bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |W (x-r) - W x + r*deriv W x|) ≤
      min 1 (θ*r) * (X.ψ θ - q)⁻¹ +
      r * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ*x)) * deriv W x) := by
  have hr0 : 0 ≤ r := hr.le
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  have hder : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * deriv W x)
      (Ioi (0 : ℝ)) :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hsigned : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        (W (x-r) - W x + r*deriv W x))
      (Ioi (0 : ℝ)) :=
    chat07_weighted_compensated_negative_jump_integrableOn
      X q W hW θ r hθ hqθ hr0
  have hker : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |W (x-r) - W x + r*deriv W x|)
      (Ioi (0 : ℝ)) := by
    have heq : (fun x : ℝ => Real.exp (-(θ*x)) *
        |W (x-r)-W x+r*deriv W x|) =
      (fun x : ℝ => |Real.exp (-(θ*x)) *
        (W (x-r)-W x+r*deriv W x)|) := by
      funext x
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [heq]
    exact hsigned.abs
  have hzero : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * W x)
      (Ioi (0 : ℝ)) := by
    simpa only [add_zero] using
      (scaleFunction_shiftedLaplace_integrable X q W hW
        θ 0 hθ hqθ le_rfl)
  have hshift : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * W (x-r))
      (Ioi (0 : ℝ)) := by
    simpa only [sub_eq_add_neg] using
      (scaleFunction_shiftedLaplace_integrable X q W hW
        θ (-r) hθ hqθ (neg_nonpos.mpr hr0))
  have hdiff : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * |W x-W (x-r)|)
      (Ioi (0 : ℝ)) := by
    have heq : (fun x : ℝ => Real.exp (-(θ*x))*|W x-W (x-r)|) =
      (fun x : ℝ => Real.exp (-(θ*x))*W x -
        Real.exp (-(θ*x))*W (x-r)) := by
      funext x
      rw [abs_of_nonneg (sub_nonneg.mpr (hmono (sub_le_self x hr0)))]
      ring
    rw [heq]
    exact hzero.sub hshift
  have htri := chat07_weighted_compensated_jump_integral_triangle
    W hmono θ r hr0 hker hdiff hder
  exact htri.trans (add_le_add
    (chat07_scale_shift_weighted_abs_integral_le_min
      X q W hW θ hθ hqθ r hr) le_rfl)
