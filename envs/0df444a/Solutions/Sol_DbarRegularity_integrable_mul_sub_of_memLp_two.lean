-- Prove2me | solution 1 for DbarRegularity.integrable_mul_sub_of_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:20:10.011969+00:00
-- url     : https://prove2.me/submissions/82cfbedd-5bef-4d42-addc-2ea1f8c938f4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- Integrability of `y ↦ K (x - y) * f y` for `K, f ∈ L²`. -/
theorem integrable_mul_sub_of_memLp_two {d : ℕ} {K f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => K (x - y) * f y) volume :=
  (hK.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).integrable_mul hf

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} {K f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => K (x - y) * f y) volume :=
  integrable_mul_sub_of_memLp_two hK hf x
