-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_strictAntiOn_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:33:11.266908+00:00
-- url     : https://prove2.me/submissions/c86a4d79-89a8-4141-9a1a-b376d66c208f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Positive logarithmic killing rate forces strict decrease of the
actual original-process reflected first-record discount in record height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      StrictAntiOn (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) (Ioi (0 : ℝ)) := by
  intro a ha b hb c hc hbc
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hrate : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hr : 0 < deriv W a / W a :=
    lt_of_lt_of_le hφ hrate
  have hmul : b * (deriv W a / W a) <
      c * (deriv W a / W a) :=
    mul_lt_mul_of_pos_right hbc hr
  have hbExp :=
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a b ha hb
  have hcExp :=
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a c ha hc
  change
    (∫⁻ ω, if twoSidedExitUpTime X c ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
      else 0 ∂P).toReal <
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P).toReal
  rw [hcExp, hbExp]
  exact Real.exp_lt_exp.mpr (neg_lt_neg hmul)
