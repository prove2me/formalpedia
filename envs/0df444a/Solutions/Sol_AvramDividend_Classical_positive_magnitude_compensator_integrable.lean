-- Prove2me | solution 1 for AvramDividend.Classical.positive_magnitude_compensator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:01:51.653373+00:00
-- url     : https://prove2.me/submissions/1e99c278-60f1-4f47-9a5a-d1caa147c91b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ) (φ : ℝ)
    (hneg : IntegrableOn
      (fun y : ℝ => 1 - Real.exp (φ * y)) (Iio (0 : ℝ)) ν) :
    Integrable (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ))))
      (ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  let f : ℝ → ℝ≥0 := fun y => Real.toNNReal (-y)
  let g : ℝ≥0 → ℝ := fun z => 1 - Real.exp (-(φ * (z : ℝ)))
  have hf : Measurable f :=
    measurable_real_toNNReal.comp measurable_neg
  have hg : AEStronglyMeasurable g (ν.map f) := by
    have hgc : Continuous g := by
      fun_prop
    exact hgc.aestronglyMeasurable
  apply (integrable_map_measure hg hf.aemeasurable).2
  have hi :
      Integrable ((Iio (0 : ℝ)).indicator
        (fun y : ℝ => 1 - Real.exp (φ * y))) ν :=
    (integrable_indicator_iff measurableSet_Iio).2 hneg
  have heq : (g ∘ f) =
      (Iio (0 : ℝ)).indicator (fun y : ℝ => 1 - Real.exp (φ * y)) := by
    funext y
    by_cases hy : y < 0
    · rw [indicator_of_mem (show y ∈ Iio (0 : ℝ) from hy)]
      simp only [Function.comp_def, g, f]
      rw [Real.coe_toNNReal _ (by linarith)]
      congr 2
      ring
    · rw [indicator_of_notMem (show y ∉ Iio (0 : ℝ) from hy)]
      simp only [Function.comp_def, g, f]
      rw [Real.toNNReal_of_nonpos (by linarith)]
      simp
  rw [heq]
  exact hi
