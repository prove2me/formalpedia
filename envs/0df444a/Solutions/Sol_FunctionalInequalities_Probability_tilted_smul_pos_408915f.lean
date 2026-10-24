-- Prove2me | solution 1 for FunctionalInequalities.Probability.tilted_smul_pos_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:23:37.599564+00:00
-- url     : https://prove2.me/submissions/420b9a14-3b54-48e9-8483-de7feeef2609

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
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
