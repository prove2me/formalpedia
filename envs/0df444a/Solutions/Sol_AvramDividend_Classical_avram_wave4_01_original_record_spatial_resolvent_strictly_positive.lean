-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:51:47.524991+00:00
-- url     : https://prove2.me/submissions/bcc0baa8-b777-48c7-8706-8025f7526cf0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The actual original killed first-record spatial potential is strictly
positive throughout the full negative-tilt-admissible Esscher half-line. -/
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
    0 < ∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal := by
  have hκ : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hden : 0 < θ + deriv W a / W a := by linarith
  rw [avram_wave4_01_original_record_spatial_exponential_moment_resolvent
      X q hq W hW hvar φ hφ hroot a θ ha hθ]
  exact inv_pos.mpr hden
