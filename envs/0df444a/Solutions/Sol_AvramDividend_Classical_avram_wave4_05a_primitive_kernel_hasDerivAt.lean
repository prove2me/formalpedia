-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_primitive_kernel_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:28:56.582579+00:00
-- url     : https://prove2.me/submissions/03139f51-7269-49f9-b98e-cf059299a7ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- For the genuine unbounded-variation source scale primitive, differentiation
of each fixed compensated jump increment commutes with its first derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
        (fun v : ℝ => ∫ t in (0 : ℝ)..v, W t) z y)
      (SpectrallyNegativeLevy.generatorIntegrand W x y) x := by
  let U : ℝ → ℝ := fun v => ∫ t in (0 : ℝ)..v, W t
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hD : ∀ z : ℝ, HasDerivAt U (W z) z := by
    intro z
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 z)
      (hcont.stronglyMeasurableAtFilter volume (nhds z))
      hcont.continuousAt
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hDW : HasDerivAt W (deriv W x) x :=
    ((hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hShift : HasDerivAt (fun z : ℝ => U (z + y)) (W (x + y)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hD (x + y)).comp x ((hasDerivAt_id x).add_const y)
  have hJ : HasDerivAt
      (fun z : ℝ => U (z + y) - U z -
        W z * (y * (Ioo (-1 : ℝ) 1).indicator 1 y))
      (W (x + y) - W x -
        deriv W x * (y * (Ioo (-1 : ℝ) 1).indicator 1 y)) x :=
    (hShift.sub (hD x)).sub
      (hDW.mul_const (y * (Ioo (-1 : ℝ) 1).indicator 1 y))
  have hGlobal : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
      X hnbv q hq W hW
  have hfun :
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand U z y) =
      (fun z : ℝ => U (z + y) - U z -
        W z * (y * (Ioo (-1 : ℝ) 1).indicator 1 y)) := by
    funext z
    simp [SpectrallyNegativeLevy.generatorIntegrand, hGlobal, mul_assoc]
  change HasDerivAt
    (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand U z y)
    (SpectrallyNegativeLevy.generatorIntegrand W x y) x
  rw [hfun]
  simpa [SpectrallyNegativeLevy.generatorIntegrand, mul_assoc] using hJ
