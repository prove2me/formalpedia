-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_singular_negative_density_isLevyMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:11:21.497787+00:00
-- url     : https://prove2.me/submissions/a1ef4597-d1ad-4f51-846b-ae018a86d35c

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_first_moment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-! The singular inverse-three-halves negative jump density is a Lévy measure. -/
theorem solution :
    ProbabilityTheory.IsLevyMeasure
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by
  let f : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0
  let ν : Measure ℝ := volume.withDensity f
  change IsLevyMeasure ν
  constructor
  · have hAC : ν.AbsolutelyContinuous volume :=
      withDensity_absolutelyContinuous volume f
    exact hAC (by simp)
  · have hI : Integrable (fun z : ℝ => |z|) ν :=
      AvramDividend.Classical.avram_gen14_singular_levy_first_moment_integrable
    have hL : (∫⁻ z, ENNReal.ofReal (|z|) ∂ν) < ⊤ := by
      simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs, abs_abs] using
        hI.hasFiniteIntegral
    calc
      (∫⁻ z, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν)
          ≤ ∫⁻ z, ENNReal.ofReal (|z|) ∂ν := by
              apply lintegral_mono
              intro z
              apply ENNReal.ofReal_le_ofReal
              by_cases hz : |z| ≤ 1
              · apply (min_le_right _ _).trans
                nlinarith [sq_abs z, abs_nonneg z]
              · exact (min_le_left _ _).trans
                  (le_of_lt (lt_of_not_ge hz))
      _ < ⊤ := hL
