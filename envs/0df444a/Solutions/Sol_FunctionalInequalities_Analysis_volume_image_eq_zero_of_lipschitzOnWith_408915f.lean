-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:01:13.168154+00:00
-- url     : https://prove2.me/submissions/cf4ae8aa-fcb8-4231-b3a3-aa2200d04e9d

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace
section LT12D1LipschitzNullImage
open MeasureTheory Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Lipschitz maps send null sets to null sets** (weak Letwin route, Alexandrov's second-order
differentiability theorem): for a map of a finite-dimensional real inner product space into
itself that is Lipschitz on `s`, a Lebesgue-null `s` has a Lebesgue-null image. No measurability of `s`
is assumed. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0 := by
  have hsH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) s = 0 := by
    rw [Measure.isAddLeftInvariant_eq_smul
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (volume : Measure E),
      Measure.smul_apply, hs, smul_zero]
  have himageH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (f '' s) = 0 := by
    have h := hf.hausdorffMeasure_image_le (Nat.cast_nonneg (Module.finrank ℝ E))
    rw [hsH, mul_zero] at h
    exact le_antisymm h bot_le
  rw [Measure.isAddLeftInvariant_eq_smul
    (volume : Measure E) (μH[(Module.finrank ℝ E : ℝ)] : Measure E),
    Measure.smul_apply, himageH, smul_zero]
