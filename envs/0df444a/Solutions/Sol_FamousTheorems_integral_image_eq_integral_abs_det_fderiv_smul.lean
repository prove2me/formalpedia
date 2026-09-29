-- Prove2me | solution 1 for FamousTheorems.integral_image_eq_integral_abs_det_fderiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:17.304715+00:00
-- url     : https://prove2.me/submissions/d3cf5bca-b528-4495-8fa5-900d0bb025a3

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} {F : Type u_2} 
    [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [inst_3 : NormedAddCommGroup F] 
    [inst_4 : NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E} [inst_5 : MeasurableSpace E] [BorelSpace E] 
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure], 
    MeasurableSet s → 
    (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) → 
    InjOn f s → ∀ (g : E → F), ∫ (x : E) in f '' s, g x ∂μ = ∫ (x : E) in s, |(f' x).det| • g (f x) ∂μ :=
  @_root_.MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
