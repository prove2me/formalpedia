-- Prove2me | solution 1 for DbarRegularity.aestronglyMeasurable_integral_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:06:45.781028+00:00
-- url     : https://prove2.me/submissions/14981133-5588-4894-a099-6b8bd0a1d4a2

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- The convolution-type integral `x ↦ ∫ K(x - y) f(y) dy` of a.e.-strongly measurable functions
is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_integral_mul_sub {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * f y) volume := by
  have h : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (p.1 - p.2) * f p.2)
      (volume.prod volume) :=
    (hK.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).mul
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact h.integral_prod_right'

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * f y) volume :=
  aestronglyMeasurable_integral_mul_sub K f hK hf
