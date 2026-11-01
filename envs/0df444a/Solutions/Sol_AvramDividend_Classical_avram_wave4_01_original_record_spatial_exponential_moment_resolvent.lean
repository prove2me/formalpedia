-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_exponential_moment_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:28:02.690686+00:00
-- url     : https://prove2.me/submissions/13422058-6885-42f1-88a7-1c6854a3494b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Genuine record-height spatial Laplace resolvent extends to
negative tilts above the Esscher threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    (∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) =
    (θ + deriv W a / W a)⁻¹ := by
  let k : ℝ := deriv W a / W a
  let F : ℝ → ℝ := fun h =>
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal
  have hkle : φ ≤ k :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hsum : 0 < θ + k := by linarith
  have hneg : -(θ + k) < 0 := by linarith
  have hexp : (∫ h : ℝ in Ioi 0,
      Real.exp ((-(θ + k)) * h)) = (θ + k)⁻¹ := by
    rw [integral_exp_mul_Ioi hneg 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  have hcongr : (∫ h : ℝ in Ioi 0, Real.exp (-(θ * h)) * F h) =
      (∫ h : ℝ in Ioi 0, Real.exp ((-(θ + k)) * h)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    have hhpos : 0 < h := hh
    have hE := avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h ha hhpos
    change F h = Real.exp (-(h * k)) at hE
    calc
      Real.exp (-(θ * h)) * F h =
          Real.exp (-(θ * h)) * Real.exp (-(h * k)) := by rw [hE]
      _ = Real.exp ((-(θ + k)) * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact hcongr.trans hexp
