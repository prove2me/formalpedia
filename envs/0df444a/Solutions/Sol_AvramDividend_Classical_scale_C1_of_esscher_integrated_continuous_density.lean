-- Prove2me | solution 1 for AvramDividend.Classical.scale_C1_of_esscher_integrated_continuous_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:10:52.763736+00:00
-- url     : https://prove2.me/submissions/96a3bc76-4728-464c-941a-8faa7d3d4bf2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- A continuous density of the Esscher-tilted renewal cumulative yields C1
regularity of the original scale function on the strictly positive axis. -/
theorem solution
    (W f : ℝ → ℝ) (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  let V : ℝ → ℝ := fun x => c + ∫ y in (0 : ℝ)..x, f y
  have hV : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    contDiffOn_one_const_add_intervalIntegral f c hcont hint
  apply esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one φ W V hV
  intro x hx
  exact (hrepr x hx).symm
