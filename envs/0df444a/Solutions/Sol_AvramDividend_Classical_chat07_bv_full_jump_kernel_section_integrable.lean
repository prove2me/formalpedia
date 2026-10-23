-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_full_jump_kernel_section_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:45:42.64403+00:00
-- url     : https://prove2.me/submissions/031ea73b-b4b3-44d5-936a-e20dce944642

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_negative_jump_integrableOn
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

-- Every positive jump magnitude has an integrable reserve section.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      (W (x-r) - W x +
        (if r < 1 then r * deriv W x else 0)))
      (Ioi (0 : ℝ)) := by
  classical
  by_cases hsmall : r < 1
  · simpa only [if_pos hsmall] using
      (chat07_weighted_compensated_negative_jump_integrableOn
        X q W hW θ r hθ hqθ hr.le)
  · have hzero : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) * W x)
        (Ioi (0 : ℝ)) := by
      simpa only [add_zero] using
        (scaleFunction_shiftedLaplace_integrable
          X q W hW θ 0 hθ hqθ le_rfl)
    have hshift : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) * W (x-r))
        (Ioi (0 : ℝ)) := by
      simpa only [sub_eq_add_neg] using
        (scaleFunction_shiftedLaplace_integrable
          X q W hW θ (-r) hθ hqθ (neg_nonpos.mpr hr.le))
    have hdiff : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) * (W (x-r)-W x))
        (Ioi (0 : ℝ)) := by
      have heq : (fun x : ℝ =>
        Real.exp (-(θ*x)) * (W (x-r)-W x)) =
          (fun x : ℝ => Real.exp (-(θ*x))*W (x-r) -
            Real.exp (-(θ*x))*W x) := by
        funext x
        ring
      rw [heq]
      exact hshift.sub hzero
    simpa only [if_neg hsmall, add_zero] using hdiff
