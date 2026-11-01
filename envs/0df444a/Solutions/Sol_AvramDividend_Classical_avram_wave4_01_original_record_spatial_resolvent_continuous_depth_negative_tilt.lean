-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_continuous_depth_negative_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:50:28.62613+00:00
-- url     : https://prove2.me/submissions/5ef417ad-b996-49fa-9db5-25f656410664

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal Topology

/-- The genuine spatial exponential height potential varies continuously
with the drawdown depth, even at negative tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ : ℝ) (hθ : -φ < θ) :
    ContinuousOn (fun a : ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) (Ioi 0) := by
  let κ : ℝ → ℝ := fun a =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                         barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hκ : ContinuousOn κ (Ioi 0) :=
    avram_wave3_01_canonical_infinite_jump_log_rate_continuous
      X q hq W hW hvar
  have hr (a : ℝ) (ha : 0 < a) : κ a = deriv W a / W a := by
    have h1 := avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a 1 ha (by norm_num)
    dsimp [κ]
    rw [h1]
    simp
  have hden : ContinuousOn (fun a : ℝ => θ + κ a) (Ioi 0) :=
    continuousOn_const.add hκ
  have hF : ContinuousOn (fun a : ℝ => (1 : ℝ) / (θ + κ a)) (Ioi 0) := by
    apply continuousOn_const.div hden
    intro a ha
    have hkle : φ ≤ deriv W a / W a :=
      avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
        X q hq W hW hvar φ hφ hroot a ha
    have hpos : 0 < θ + κ a := by rw [hr a ha]; linarith
    exact ne_of_gt hpos
  apply hF.congr
  intro a ha
  change (∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) = (1 : ℝ) / (θ + κ a)
  rw [hr a ha]
  simpa only [one_div] using
    (avram_wave4_01_original_record_spatial_exponential_moment_resolvent
      X q hq W hW hvar φ hφ hroot a θ ha hθ)
