-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:09:11.127975+00:00
-- url     : https://prove2.me/submissions/e5144dd5-8fa7-424e-acf6-2beaacc34c5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_interval_reflection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The real compensated scale-primitive integrand is the W' tent kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hrx : r < x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r) =
      ∫ s in (0 : ℝ)..r, (r - s) *
        ((Ioi (0 : ℝ)).indicator (deriv W)) (x - s) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (deriv W)
  have hInterior :=
    avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
      X hX q hq W hW r x hr0 hr1 hrx
  have hInterval :
      (∫ t in (x - r)..x, (t - (x-r)) * iteratedDeriv 2 U t) =
      ∫ t in (x-r)..x, (t-(x-r)) * F t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hle : x-r ≤ x := by linarith
    have hpos : 0 < t := by
      have ht' : t ∈ Icc (x-r) x := by
        simpa [Set.uIcc_of_le hle] using ht
      exact lt_of_lt_of_le (by linarith) ht'.1
    change (t-(x-r)) * iteratedDeriv 2 U t = (t-(x-r)) * F t
    rw [avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
      X q W hW t hpos]
    simp [F, Set.indicator, hpos]
  calc
    SpectrallyNegativeLevy.generatorIntegrand U x (-r) =
      ∫ t in (x-r)..x, (t-(x-r)) * iteratedDeriv 2 U t := hInterior
    _ = ∫ t in (x-r)..x, (t-(x-r)) * F t := hInterval
    _ = ∫ s in (0 : ℝ)..r, (r-s) * F (x-s) :=
      avram_wave3_05_tent_interval_reflection F x r
