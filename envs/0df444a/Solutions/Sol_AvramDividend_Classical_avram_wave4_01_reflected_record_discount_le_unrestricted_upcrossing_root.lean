-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:22:35.773959+00:00
-- url     : https://prove2.me/submissions/23e497e2-37f2-47b8-b34f-ee0143f23636

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine reflected killing only removes paths from the unrestricted
strict first-passage Laplace transform at its positive root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < b →
      (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * b))) := by
  intro a b hb
  have hle :
      (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTimeCorrected X b ω <
                    (⊤ : ℝ≥0∞) then
          ENNReal.ofReal
            (Real.exp (-(q *
              (twoSidedExitUpTimeCorrected X b ω).toReal)))
        else 0 ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases h : twoSidedExitUpTime X b ω <
        barrierRuinTime X a ω
    · have hu : twoSidedExitUpTimeCorrected X b ω < (⊤ : ℝ≥0∞) :=
        lt_of_lt_of_le h le_top
      simp only [if_pos h, if_pos hu]
      exact le_refl _
    · simp only [if_neg h]
      exact bot_le
  have htransform :=
    levy_positive_root_exact_strict_upcrossing_discount
      X q hq φ hφ hroot b hb
  rw [htransform] at hle
  exact hle
