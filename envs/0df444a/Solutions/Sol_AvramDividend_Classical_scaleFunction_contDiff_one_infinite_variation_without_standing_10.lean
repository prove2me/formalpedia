-- Prove2me | solution 10 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:40:24.576825+00:00
-- url     : https://prove2.me/submissions/e6ba4022-4ef5-470e-99f8-6602569dddbd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_log_derivative_to_scale_C1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- Standing-free pure small-jump C¹, now factored through the genuine source sandwich. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun a h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  let κ : ℝ → ℝ := fun a => -Real.log ((F a 1).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hWpos : ∀ a : ℝ, 0 < a → 0 < W a := by
    intro a ha
    exact scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
  have hκ : ContinuousOn κ (Ioi (0 : ℝ)) := by
    simpa only [κ, F] using
      (avram_wave3_01_canonical_infinite_jump_log_rate_continuous
        X q hq W hW hvar)
  have hFdef : ∀ a h : ℝ, F a h =
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P := by intros; rfl
  have hκdef : ∀ a : ℝ, κ a = -Real.log ((F a 1).toReal) := by
    intro a
    rfl
  have hsand := avram_wave4_01_genuine_local_scale_ratio_sandwich
    X q hq W hW hvar F hFdef κ hκdef
  have hlog := avram_wave4_01_local_exponential_scale_sandwich_log_deriv
    W κ hWpos hκ hsand
  exact avram_wave3_01_log_derivative_to_scale_C1 W κ hWpos hκ hlog
