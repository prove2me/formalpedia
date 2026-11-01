-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_log_hazard_antitone_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:32:08.69793+00:00
-- url     : https://prove2.me/submissions/cb045725-f520-40ef-9d73-cbfa4c7b6d9b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_monotone_drawdown_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On positive depths the genuine first-record killing exponent is
antitone, by actual ruin-clock monotonicity and positive finite discounts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    AntitoneOn
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      (Ioi (0 : ℝ)) := by
  let F : ℝ → ℝ≥0∞ := fun a =>
    ∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P
  change AntitoneOn (fun a : ℝ => -Real.log ((F a).toReal))
    (Ioi (0 : ℝ))
  intro a ha b hb hab
  have hmono : F a ≤ F b := by
    simpa only [F] using
      (avram_wave4_01_original_record_discount_monotone_drawdown_depth
        X q 1 a b hab)
  have hboundA : F a ≤ 1 := by
    simpa only [F] using
      (avram_wave3_01_original_record_discount_le_one
        X q hq a 1)
  have hboundB : F b ≤ 1 := by
    simpa only [F] using
      (avram_wave3_01_original_record_discount_le_one
        X q hq b 1)
  have hfinA : F a ≠ ⊤ :=
    (lt_top_iff_ne_top).mp (lt_of_le_of_lt hboundA (by simp))
  have hfinB : F b ≠ ⊤ :=
    (lt_top_iff_ne_top).mp (lt_of_le_of_lt hboundB (by simp))
  have hpositiveA : 0 < F a := by
    simpa only [F] using
      (avram_wave3_01_reflected_record_discount_strict_pos
        X q hq W hW hnbv a ha 1 (by norm_num))
  have hrealA : 0 < (F a).toReal :=
    ENNReal.toReal_pos (ne_of_gt hpositiveA) hfinA
  have hrealmono : (F a).toReal ≤ (F b).toReal :=
    ENNReal.toReal_mono hfinB hmono
  exact neg_le_neg (Real.log_le_log hrealA hrealmono)
