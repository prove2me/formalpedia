-- Prove2me | solution 1 for FamousTheorems.frullani_integral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:34:44.223087+00:00
-- url     : https://prove2.me/submissions/7de1c9a9-6c03-450b-89c0-758666168dc6

import Mathlib

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ} {L R : E}
    (hf : LocallyIntegrableOn f (Set.Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) (hR : Filter.Tendsto f Filter.atTop (nhds R))
    (hint : IntegrableOn (fun x : ℝ => x⁻¹ • (f (a * x) - f (b * x))) (Set.Ioi 0)) :
    ∫ x in Set.Ioi (0 : ℝ), x⁻¹ • (f (a * x) - f (b * x)) = Real.log (b / a) • (L - R) :=
  Frullani.integral_Ioi_eq hf ha hb hL hR hint
