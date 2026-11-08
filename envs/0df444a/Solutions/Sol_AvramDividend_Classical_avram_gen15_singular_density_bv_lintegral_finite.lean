-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_singular_density_bv_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:25:13.450208+00:00
-- url     : https://prove2.me/submissions/da0fff3e-5a6d-4d30-9ed7-626bd4a762b3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_absolute_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_first_moment_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The explicit singular density satisfies the source bounded-variation Levy criterion. -/
theorem solution :
    (∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal |z| ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) < ⊤ := by
  let ν : Measure ℝ := volume.withDensity (fun z : ℝ =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
  change (∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal |z| ∂ν) < ⊤
  have hfi : Integrable (fun z : ℝ => |z|) ν := by
    simpa only [ν] using
      avram_gen14_singular_levy_first_moment_integrable
  have hm : (∫ z : ℝ, |z| ∂ν) = 2 := by
    simpa only [ν] using
      avram_gen14_singular_levy_absolute_first_moment
  have htotal : (∫⁻ z, ENNReal.ofReal |z| ∂ν) = ENNReal.ofReal 2 := by
    calc
      (∫⁻ z, ENNReal.ofReal |z| ∂ν) = ENNReal.ofReal (∫ z, |z| ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hfi
          (Filter.Eventually.of_forall (fun z => abs_nonneg z))).symm
      _ = ENNReal.ofReal 2 := by rw [hm]
  calc
    (∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal |z| ∂ν) ≤
        (∫⁻ z, ENNReal.ofReal |z| ∂ν) := by
          simpa only [Measure.restrict_univ] using
            (lintegral_mono_set (μ := ν) (f := fun z : ℝ => ENNReal.ofReal |z|)
              (Set.subset_univ (Ioo (-1 : ℝ) 0)))
    _ = ENNReal.ofReal 2 := htotal
    _ < ⊤ := ENNReal.ofReal_lt_top
