-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:59:18.550988+00:00
-- url     : https://prove2.me/submissions/62d43a0a-847d-4998-aba0-ae994afb7f3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_scaleFunction_of_contDiffOn_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- The missing genuine original pure-jump local scale generator harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  obtain ⟨β, hβ, hψβ⟩ := psi_eventually_gt_of_standing X hX q hq
  have hb : 0 < β + 1 := by linarith
  have hUres :=
    avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
      X hX hnbv q hq W hW (β + 1) hb (by
        intro θ hθ
        exact avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
          X hX hσ hnbv q hq W hW θ (by linarith) (hψβ θ (by linarith)))
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let K : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ),
    SpectrallyNegativeLevy.generatorIntegrand U z y ∂X.ν
  have hGlobal : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
      X hnbv q hq W hW
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hDU : ∀ z : ℝ, HasDerivAt U (W z) z := by
    intro z
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 z)
      (hcont.stronglyMeasurableAtFilter volume (nhds z))
      hcont.continuousAt
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hGenU (z : ℝ) : X.generator U z = X.c * W z + K z := by
    unfold SpectrallyNegativeLevy.generator
    simp [hσ, hGlobal, K]
  intro x hx
  have hInt := generatorIntegrable_scaleFunction_of_contDiffOn_two
    X q W hW a hC2 x hx
  refine ⟨hInt, ?_⟩
  have hl : 0 < x / 2 := by linarith [hx.1]
  have hlu : x / 2 < (x + a) / 2 := by linarith [hx.2]
  have hu : (x + a) / 2 < a := by linarith [hx.2]
  have hxin : x ∈ Ioo (x / 2) ((x + a) / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hK : HasDerivAt K
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) x := by
    simpa only [K, U] using
      (avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
        X hX hnbv q hq W hW a (x / 2) ((x + a) / 2)
        hl hlu hu hC2 x hxin)
  have hDW : HasDerivAt W (deriv W x) x :=
    ((hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx.1)).hasDerivAt
  have hResDeriv : HasDerivAt
      (fun z : ℝ => X.c * W z + K z - q * U z)
      (X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * W x) x :=
    ((hDW.const_mul X.c).add hK).sub ((hDU x).const_mul q)
  have hFunEq :
      (fun z : ℝ => X.generator U z - q * U z) =
      (fun z : ℝ => X.c * W z + K z - q * U z) := by
    funext z
    rw [hGenU]
  have hResAt : HasDerivAt (fun z : ℝ => X.generator U z - q * U z)
      (X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * W x) x := by
    rw [hFunEq]
    exact hResDeriv
  have hevent :
      (fun z : ℝ => X.generator U z - q * U z) =ᶠ[nhds x]
        (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx.1] with z hz
    exact hUres z hz
  have hderiv0 :
      deriv (fun z : ℝ => X.generator U z - q * U z) x = 0 := by
    rw [hevent.deriv_eq]
    simp
  have hzeroeq := hResAt.deriv
  rw [hderiv0] at hzeroeq
  have hGenW : X.generator W x =
      X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) := by
    unfold SpectrallyNegativeLevy.generator
    simp [hσ]
  rw [hGenW]
  linarith
