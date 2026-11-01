-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_exp_log_scale_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:41:51.312467+00:00
-- url     : https://prove2.me/submissions/18dc5c81-66b4-4f78-971c-d81730d1c70a

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_eq_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact uncapped first-record semigroup is exp of the ordinary
logarithmic scale-function derivative at the actual reflected ruin depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal =
      Real.exp (-(h * (deriv W a / W a))) := by
  intro a h ha hh
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hpos : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv a ha
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_infinite_variation_without_standing
      X q hq W hW hvar
  have hpoint : ContDiffAt ℝ 1 W a :=
    hC1.contDiffAt (isOpen_Ioi.mem_nhds ha)
  have hdiff : DifferentiableAt ℝ W a :=
    hpoint.differentiableAt (by norm_num)
  have hlogFromW :
      HasDerivAt (fun z : ℝ => Real.log (W z))
        (deriv W a / W a) a :=
    hdiff.hasDerivAt.log (ne_of_gt hpos)
  have hlogFromRecord :
      HasDerivAt (fun z : ℝ => Real.log (W z))
        (-Real.log
          ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal)) a :=
    avram_wave4_01_original_record_hazard_eq_log_scale_deriv
      X q hq W hW hvar a ha
  have hrate :
      -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) = deriv W a / W a :=
    hlogFromRecord.deriv.symm.trans hlogFromW.deriv
  have hExp := avram_wave4_01_original_record_exponential_hazard
    X q hq W hW hvar a ha h hh
  rw [hrate] at hExp
  simpa only [neg_mul] using hExp
