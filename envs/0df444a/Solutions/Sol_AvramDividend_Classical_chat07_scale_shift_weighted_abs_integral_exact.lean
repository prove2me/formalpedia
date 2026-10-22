-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:12:11.922946+00:00
-- url     : https://prove2.me/submissions/06c0ce5b-81a5-4981-8c83-615def7b8ce8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Exact weighted L1 displacement identity for the monotone q-scale function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * |W x - W (x - r)|) =
      (1 - Real.exp (-(θ * r))) * (X.ψ θ - q)⁻¹ := by
  have hm : Monotone W := scaleFunction_monotone X q W hW
  have hI0 : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi 0) := by
    simpa only [add_zero] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ 0 hθ hqθ le_rfl)
  have hIr : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W (x - r)) (Ioi 0) := by
    simpa only [sub_eq_add_neg] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ (-r) hθ hqθ (neg_nonpos.mpr (le_of_lt hr)))
  have h0 :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) =
        (X.ψ θ - q)⁻¹ := by
    simpa only [add_zero, mul_zero, Real.exp_zero, one_mul] using
      (scaleFunction_shifted_laplace_transform
        X q W hW θ 0 hθ hqθ le_rfl)
  have hR :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x - r)) =
        Real.exp (-(θ * r)) * (X.ψ θ - q)⁻¹ := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (scaleFunction_shifted_laplace_transform
        X q W hW θ (-r) hθ hqθ (neg_nonpos.mpr (le_of_lt hr)))
  calc
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * |W x - W (x - r)|) =
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-(θ * x)) * W x -
           Real.exp (-(θ * x)) * W (x - r)) := by
          congr 1
          ext x
          rw [abs_of_nonneg (sub_nonneg.mpr
            (hm (sub_le_self x (le_of_lt hr))))]
          ring
    _ = (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x - r)) := by
          rw [MeasureTheory.integral_sub hI0 hIr]
    _ = (1 - Real.exp (-(θ * r))) * (X.ψ θ - q)⁻¹ := by
          rw [h0, hR]
          ring
