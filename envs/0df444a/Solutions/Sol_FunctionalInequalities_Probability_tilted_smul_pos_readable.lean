-- Prove2me | solution 1 for FunctionalInequalities.Probability.tilted_smul_pos_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:01.161995+00:00
-- url     : https://prove2.me/submissions/1185ef75-6e59-4167-b956-b45495d6ed7b

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- A positive scalar multiple of the base measure has the same normalized tilt. -/
theorem solution {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal c • μ).tilted f = μ.tilted f := by
  unfold Measure.tilted
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, withDensity_smul_measure,
    ← withDensity_smul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  change ENNReal.ofReal c * ENNReal.ofReal
    (Real.exp (f x) / (c * ∫ y, Real.exp (f y) ∂μ)) =
      ENNReal.ofReal (Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ)
  rw [← ENNReal.ofReal_mul hc.le]
  congr 1
  by_cases hZ : (∫ y, Real.exp (f y) ∂μ) = 0
  · simp [hZ]
  · field_simp [hc.ne', hZ]
