-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_deriv_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:29:55.641957+00:00
-- url     : https://prove2.me/submissions/0742e533-3be7-4a15-b5af-668783a9a2d1

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_derivative_jump_convolution_identity
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The differentiated renewal equation and vanishing explicit jump convolution fix the derivative limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun x : ℝ => deriv W x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + (X.ν (Iio (0 : ℝ))).toReal) / (X.drift ^ 2))) := by
  let d : ℝ := X.drift
  let l : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let G : ℝ → ℝ := fun x =>
    ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν
  have hd : d ≠ 0 := ne_of_gt (bv_standing_drift_pos X hX hBV).1
  have h0 : W 0 = 1 / d := bv_scale_origin_eq_inv_drift X hX q hq W hW hBV
  have hWcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0 :=
    (hW.2.2.1.continuousWithinAt (by simp)).mono
      (by intro x hx; exact le_of_lt (mem_Ioi.mp hx))
  have hG : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    bv_finite_activity_scale_jump_convolution_tendsto_zero
      X hX q hq W hW hBV hFinite
  have hderiv : ∀ x : ℝ, 0 < x →
      d * deriv W x = (q + l) * W x - G x :=
    bv_finite_activity_scale_derivative_jump_convolution_identity
      X hX q hq W hW hBV hFinite
  have hnum : Tendsto (fun x : ℝ => (q + l) * W x - G x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + l) * W 0 - 0)) := by
    have hc : Tendsto (fun _ : ℝ => q + l)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (q + l)) :=
      tendsto_const_nhds
    have ht := (hc.mul hWcont.tendsto).sub hG
    change Tendsto (fun x : ℝ => (q + l) * W x - G x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + l) * W 0 - 0)) at ht
    exact ht
  have hdiv : Tendsto
      (fun x : ℝ => ((q + l) * W x - G x) / d)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (((q + l) * W 0 - 0) / d)) := by
    have ht := hnum.div_const d
    change Tendsto (fun x : ℝ => ((q + l) * W x - G x) / d)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (((q + l) * W 0 - 0) / d)) at ht
    exact ht
  have hgoal : ((q + l) * W 0 - 0) / d = (q + l) / d ^ 2 := by
    rw [h0]
    field_simp [hd]
    ring
  have heq : (fun x : ℝ => deriv W x) =ᶠ[
      nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => ((q + l) * W x - G x) / d) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply (eq_div_iff hd).mpr
    simpa [mul_comm] using hderiv x (mem_Ioi.mp hx)
  have hresult : Tendsto (fun x : ℝ => deriv W x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + l) / d ^ 2)) := by
    simpa only [hgoal] using (hdiv.congr' heq.symm)
  simpa only [d, l] using hresult
