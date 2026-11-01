-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_joint_continuous_tilt_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:06:13.107437+00:00
-- url     : https://prove2.me/submissions/d56ac6bd-7c6a-46cb-bd52-5c8ce9a9c8e0

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
/-- Genuine first-record spatial resolvent: joint tilt-depth continuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(p.1 * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X p.2 ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      {p : ℝ × ℝ | -φ < p.1 ∧ 0 < p.2} := by
  let κ : ℝ → ℝ := fun a =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                         barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hκ : ContinuousOn κ (Ioi 0) :=
    avram_wave3_01_canonical_infinite_jump_log_rate_continuous X q hq W hW hvar
  have hr (a : ℝ) (ha : 0 < a) : κ a = deriv W a / W a := by
    have h1 := avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a 1 ha (by norm_num)
    dsimp [κ]; rw [h1]; simp
  let S : Set (ℝ × ℝ) := {p | -φ < p.1 ∧ 0 < p.2}
  have hfirst : ContinuousOn (fun p : ℝ × ℝ => p.1) S := continuous_fst.continuousOn
  have hsecond : ContinuousOn (fun p : ℝ × ℝ => κ p.2) S :=
    hκ.comp continuous_snd.continuousOn (by intro p hp; exact hp.2)
  have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 + κ p.2) S := by
    apply (hfirst.add hsecond).congr
    intro p hp; simp only [Pi.add_apply]
  have hF : ContinuousOn (fun p : ℝ × ℝ =>
      (1 : ℝ) / (p.1 + κ p.2)) S := by
    apply continuousOn_const.div hden
    intro p hp
    have hkle : φ ≤ deriv W p.2 / W p.2 :=
      avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
        X q hq W hW hvar φ hφ hroot p.2 hp.2
    have hpos : 0 < p.1 + κ p.2 := by rw [hr p.2 hp.2]; linarith [hp.1]
    exact ne_of_gt hpos
  change ContinuousOn (fun p : ℝ × ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(p.1 * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X p.2 ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) S
  apply hF.congr
  intro p hp
  change (∫ h : ℝ in Ioi 0,
      Real.exp (-(p.1 * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X p.2 ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) = (1 : ℝ) / (p.1 + κ p.2)
  rw [hr p.2 hp.2]
  simpa only [one_div] using
    (avram_wave4_01_original_record_spatial_exponential_moment_resolvent
      X q hq W hW hvar φ hφ hroot p.2 p.1 hp.2 hp.1)
