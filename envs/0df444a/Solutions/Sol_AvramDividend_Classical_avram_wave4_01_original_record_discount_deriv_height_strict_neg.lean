-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_deriv_height_strict_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:34:44.431168+00:00
-- url     : https://prove2.me/submissions/d1bede1d-881b-46d3-ba5e-af9447e034e8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_height_ode

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original-process reflected first-record survival has strictly
negative ordinary derivative in every positive record-height direction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      deriv (fun b : ℝ =>
          (∫⁻ ω, if twoSidedExitUpTime X b ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
          else 0 ∂P).toReal) h < 0 := by
  intro a h ha hh
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hrate : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hr : 0 < deriv W a / W a :=
    lt_of_lt_of_le hφ hrate
  have hexact :=
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h ha hh
  have hmass : 0 <
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal := by
    rw [hexact]
    exact Real.exp_pos _
  have hode :=
    avram_wave4_01_original_record_discount_height_ode
      X q hq W hW hvar a h ha hh
  rw [hode.deriv]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hr) hmass
