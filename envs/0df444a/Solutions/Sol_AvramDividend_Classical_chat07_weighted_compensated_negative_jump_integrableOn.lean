-- Prove2me | solution 1 for AvramDividend.Classical.chat07_weighted_compensated_negative_jump_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:46:21.551338+00:00
-- url     : https://prove2.me/submissions/b8890e2c-5db7-4537-8112-f51d3a67d82f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Every fixed negative jump has an integrable weighted compensated kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 ≤ r) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (W (x - r) - W x + r * deriv W x))
      (Ioi (0 : ℝ)) := by
  have hshift :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x - r))
        (Ioi (0 : ℝ)) := by
    simpa only [sub_eq_add_neg] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ (-r) hθ hqθ (neg_nonpos.mpr hr))
  have hzero :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x)
        (Ioi (0 : ℝ)) := by
    simpa only [add_zero] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ 0 hθ hqθ le_rfl)
  have hderiv :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
        (Ioi (0 : ℝ)) :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hsum : IntegrableOn
      (fun x : ℝ =>
        (Real.exp (-(θ * x)) * W (x-r) -
         Real.exp (-(θ * x)) * W x) +
         r * (Real.exp (-(θ * x)) * deriv W x))
      (Ioi (0 : ℝ)) :=
    (hshift.sub hzero).add (hderiv.const_mul r)
  have heq :
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (W (x-r) - W x + r * deriv W x)) =
      (fun x : ℝ =>
        (Real.exp (-(θ * x)) * W (x-r) -
         Real.exp (-(θ * x)) * W x) +
         r * (Real.exp (-(θ * x)) * deriv W x)) := by
    funext x
    ring
  rw [heq]
  exact hsum
