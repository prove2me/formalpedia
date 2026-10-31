-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_convolution_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:53:37.777618+00:00
-- url     : https://prove2.me/submissions/5d6108ed-77a0-45a4-afe7-ef8736daff4f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-- A jointly measurable translated Lévy kernel has a measurable
    compact Taylor-tent integral as a function of its reserve. -/
theorem solution
    (F : ℝ → ℝ) (hF : Measurable F)
    (r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun x : ℝ =>
      ∫ s in (0 : ℝ)..r, (r - s) * F (x - s)) := by
  have huncurry :
      StronglyMeasurable (Function.uncurry
        (fun x s : ℝ => (r - s) * F (x - s))) := by
    have hm : Measurable
        (fun p : ℝ × ℝ => (r - p.2) * F (p.1 - p.2)) :=
      (measurable_const.sub measurable_snd).mul
        (hF.comp (measurable_fst.sub measurable_snd))
    exact hm.stronglyMeasurable
  have hmeas : StronglyMeasurable (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) r, (r - s) * F (x - s)) :=
    huncurry.integral_prod_right (ν := volume.restrict (Ioc 0 r))
  simpa only [← intervalIntegral.integral_of_le hr] using hmeas.measurable
