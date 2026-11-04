-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:17:59.845673+00:00
-- url     : https://prove2.me/submissions/ddbdbeb3-6042-455d-8879-28bf798590f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The source Levy measure, restricted to negative marks and weighted
by the fourth exponential deficit, gives a finite pushforward under exp. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    IsFiniteMeasure
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp) := by
  let g : ℝ → ℝ → ℝ := fun r y => Real.exp (r * y) - 1 -
    r * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hw : IntegrableOn (fun y : ℝ => min 1 (y ^ 2))
      (Iio (0 : ℝ)) X.ν := (levyWeight_integrable X).integrableOn
  have hint (r : ℝ) (hr : 0 ≤ r) :
      IntegrableOn (g r) (Iio (0 : ℝ)) X.ν := by
    have h := levy_exponential_generatorIntegrable_of_moment X r 0 hr hw
    change IntegrableOn (fun y : ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => Real.exp (r * z)) 0 y) (Iio (0 : ℝ)) X.ν at h
    simpa only [g, generatorIntegrand_exp_mul, mul_zero,
      Real.exp_zero, one_mul] using h
  have h0 := hint 0 (by norm_num)
  have h1 := hint 1 (by norm_num)
  have h2 := hint 2 (by norm_num)
  have h3 := hint 3 (by norm_num)
  have h4 := hint 4 (by norm_num)
  have hp (y : ℝ) :
      g 4 y - 4 * g 3 y + 6 * g 2 y - 4 * g 1 y + g 0 y =
        (Real.exp y - 1) ^ 4 := by
    have e2 : Real.exp (2 * y) = (Real.exp y) ^ 2 := by
      simpa using (Real.exp_nat_mul y 2)
    have e3 : Real.exp (3 * y) = (Real.exp y) ^ 3 := by
      simpa using (Real.exp_nat_mul y 3)
    have e4 : Real.exp (4 * y) = (Real.exp y) ^ 4 := by
      simpa using (Real.exp_nat_mul y 4)
    dsimp [g]
    rw [e2, e3, e4]
    simp only [zero_mul, Real.exp_zero, zero_sub]
    ring
  have hF : IntegrableOn
      (fun y => g 4 y - 4 * g 3 y + 6 * g 2 y -
        4 * g 1 y + g 0 y) (Iio (0 : ℝ)) X.ν :=
    (((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
      (h1.const_mul 4)).add h0
  have he : (fun y : ℝ => g 4 y - 4 * g 3 y + 6 * g 2 y -
      4 * g 1 y + g 0 y) =
      (fun y : ℝ => (Real.exp y - 1) ^ 4) := funext hp
  rw [he] at hF
  letI : IsFiniteMeasure
      ((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))) :=
    isFiniteMeasure_withDensity_ofReal hF.hasFiniteIntegral
  exact Measure.isFiniteMeasure_map _ _
