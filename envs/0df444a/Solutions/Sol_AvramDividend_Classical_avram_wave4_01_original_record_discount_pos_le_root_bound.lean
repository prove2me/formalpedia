-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_pos_le_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:33:56.142212+00:00
-- url     : https://prove2.me/submissions/c7c4f7ad-86ba-4a3e-b621-e40b7eb98bfc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original first-record discount is a positive exponential, and
its reflected killing makes it no larger than unrestricted upcrossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      0 < (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal ∧
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal ≤ Real.exp (-(φ * h)) := by
  intro a h ha hh
  have hExp :=
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h ha hh
  have hBound :=
    avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
      X q hq φ hφ hroot a h hh
  constructor
  · rw [hExp]
    exact Real.exp_pos _
  · have hReal := ENNReal.toReal_mono (by simp) hBound
    simpa only [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] using hReal
