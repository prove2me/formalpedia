-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_hazard_eq_log_scale_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:22:14.553385+00:00
-- url     : https://prove2.me/submissions/9b1132be-b0a0-4e3a-8a8a-72321c7a2484

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact first-record discount hazard is the ordinary logarithmic
derivative of the original pure infinite-small-jump q-scale function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      HasDerivAt (fun z : ℝ => Real.log (W z))
        (-Real.log
          ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                      barrierRuinTime X a ω then
              ENNReal.ofReal
                (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
            else 0 ∂P).toReal)) a := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun a h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  let κ : ℝ → ℝ := fun a => -Real.log ((F a 1).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hWpos : ∀ a : ℝ, 0 < a → 0 < W a := by
    intro a ha
    exact scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hnbv a ha
  have hκ : ContinuousOn κ (Ioi (0 : ℝ)) := by
    simpa only [κ, F] using
      (avram_wave3_01_canonical_infinite_jump_log_rate_continuous
        X q hq W hW hvar)
  have hF :
      ∀ a h : ℝ, F a h =
        ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P := by
    intro a h
    rfl
  have hκdef : ∀ a : ℝ, κ a = -Real.log ((F a 1).toReal) := by
    intro a
    rfl
  have hsand : ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a))) :=
    avram_wave4_01_genuine_local_scale_ratio_sandwich
      X q hq W hW hvar F hF κ hκdef
  have hlog := avram_wave4_01_local_exponential_scale_sandwich_log_deriv
    W κ hWpos hκ hsand
  simpa only [κ, F] using hlog
