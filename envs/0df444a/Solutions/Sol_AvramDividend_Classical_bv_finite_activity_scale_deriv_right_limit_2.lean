-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_scale_deriv_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:29:24.433309+00:00
-- url     : https://prove2.me/submissions/09d874dd-2f66-4de5-af21-140a18439ff7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_derivative_jump_convolution_identity
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
import Mathlib.Topology.Algebra.Order.Field

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

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
  let A : ℝ := q + (X.ν (Iio (0 : ℝ))).toReal
  let G : ℝ → ℝ := fun x =>
    ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hdne : X.drift ≠ 0 := ne_of_gt hd
  have hW0 : W 0 = 1 / X.drift :=
    bv_scale_origin_eq_inv_drift X hX q hq W hW hBV
  have hWcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0 :=
    (hW.2.2.1.continuousWithinAt (by simp)).mono
      (by intro x hx; exact le_of_lt (mem_Ioi.mp hx))
  have hWt : Tendsto W l (nhds (W 0)) := hWcont.tendsto
  have hGt : Tendsto G l (nhds 0) :=
    bv_finite_activity_scale_jump_convolution_tendsto_zero
      X hX q hq W hW hBV hFinite
  have hEq : (fun x : ℝ => deriv W x) =ᶠ[l]
      (fun x : ℝ => (A * W x - G x) / X.drift) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hh :=
      bv_finite_activity_scale_derivative_jump_convolution_identity
        X hX q hq W hW hBV hFinite x (mem_Ioi.mp hx)
    change X.drift * deriv W x = A * W x - G x at hh
    apply (eq_div_iff hdne).2
    nlinarith
  have ht : Tendsto (fun x : ℝ => (A * W x - G x) / X.drift)
      l (nhds ((A * W 0 - 0) / X.drift)) :=
    (((tendsto_const_nhds.mul hWt).sub hGt).div_const X.drift)
  have htarget : (A * W 0 - 0) / X.drift = A / X.drift ^ 2 := by
    rw [hW0]
    field_simp [hdne]
    ring
  rw [← htarget]
  exact ht.congr' hEq.symm
