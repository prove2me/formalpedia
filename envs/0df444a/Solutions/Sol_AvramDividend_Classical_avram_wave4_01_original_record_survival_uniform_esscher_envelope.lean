-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_survival_uniform_esscher_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:08:57.356962+00:00
-- url     : https://prove2.me/submissions/d26c56e5-21df-4b8b-831e-3a477387a288

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

/-- A source-pathwise record hazard gives an integrable Esscher envelope
uniform in the reflected drawdown depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫⁻ ω, if twoSidedExitUpTime X h ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal ≤ Real.exp (-(φ * h)) := by
  have hEq := avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
  have hκ : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  rw [hEq]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hκ (le_of_lt hh)
  nlinarith
