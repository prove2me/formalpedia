-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_survival_joint_continuous_height_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:36:51.435192+00:00
-- url     : https://prove2.me/submissions/71288fe7-88ed-4c39-a9e4-eca89144e6b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal Topology

/-- Genuine discounted first-record survival varies jointly continuously
in positive height and drawdown depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X p.1 ω <
                  barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0 ∂P).toReal)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  let κ : ℝ → ℝ := fun a =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                        barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hκ : ContinuousOn κ (Ioi (0 : ℝ)) :=
    avram_wave3_01_canonical_infinite_jump_log_rate_continuous
      X q hq W hW hvar
  have hr (a : ℝ) (ha : 0 < a) : κ a = deriv W a / W a := by
    have h1 := avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a 1 ha (by norm_num)
    dsimp [κ]
    rw [h1]
    simp
  have hκcomp : ContinuousOn (fun p : ℝ × ℝ => κ p.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    hκ.comp continuous_snd.continuousOn (by
      intro p hp
      exact hp.2)
  have hF : ContinuousOn
      (fun p : ℝ × ℝ => Real.exp (-(p.1 * κ p.2)))
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    simpa only [Function.comp_def, Pi.neg_apply, Pi.mul_apply] using
      (Real.continuous_exp.comp_continuousOn
        ((continuous_fst.continuousOn.mul hκcomp).neg))
  apply hF.congr
  intro p hp
  change (∫⁻ ω, if twoSidedExitUpTime X p.1 ω <
                barrierRuinTime X p.2 ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
    else 0 ∂P).toReal = Real.exp (-(p.1 * κ p.2))
  rw [hr p.2 hp.2]
  exact avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar p.2 p.1 hp.2 hp.1
