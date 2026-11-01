-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:15:21.482246+00:00
-- url     : https://prove2.me/submissions/dfb449bc-26ad-442d-923f-f7329448bf2a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Killing the genuine strict first record at reflected ruin can only
lower its discount, so its logarithmic killing rate dominates the
unrestricted positive-root first-passage rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a : ℝ, 0 < a → φ ≤ deriv W a / W a := by
  intro a ha
  have hle :
      (∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTimeCorrected X 1 ω <
                    (⊤ : ℝ≥0∞) then
          ENNReal.ofReal
            (Real.exp (-(q *
              (twoSidedExitUpTimeCorrected X 1 ω).toReal)))
        else 0 ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases h : twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω
    · have hu : twoSidedExitUpTimeCorrected X 1 ω < (⊤ : ℝ≥0∞) :=
        lt_of_lt_of_le h le_top
      simp only [if_pos h, if_pos hu]
      exact le_refl _
    · simp only [if_neg h]
      exact bot_le
  have hunrestricted :=
    levy_positive_root_exact_strict_upcrossing_discount
      X q hq φ hφ hroot 1 (by norm_num)
  rw [hunrestricted] at hle
  have hreal : (∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal ≤ Real.exp (-(φ * 1)) := by
    have := ENNReal.toReal_mono (by simp) hle
    simpa only [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] using this
  have hexact :=
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a 1 ha (by norm_num)
  rw [hexact] at hreal
  have hlog : -(1 * (deriv W a / W a)) ≤ -(φ * 1) :=
    Real.exp_le_exp.mp hreal
  nlinarith
