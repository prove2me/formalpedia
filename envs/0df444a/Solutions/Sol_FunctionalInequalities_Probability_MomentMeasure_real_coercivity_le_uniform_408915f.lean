-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.real_coercivity_le_uniform_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:59.767499+00:00
-- url     : https://prove2.me/submissions/c9a7e438-e406-4934-831e-2377f1b56807

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- A finite real ceiling for the normalized coercivity expression. -/
theorem solution (A : ℝ) (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    Real.log A + (n : ℝ) * Real.log (max M 1) - M ≤
      Real.log A + (n : ℝ) * Real.log (2 * ((n : ℝ) + 1)) := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd1 : 1 ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := zero_lt_one.trans_le hd1
  by_cases hs : M ≤ 1
  · rw [max_eq_right hs, Real.log_one, mul_zero]
    have hlog : 0 ≤ (n : ℝ) * Real.log d := mul_nonneg hn (Real.log_nonneg hd1)
    change Real.log A + 0 - M ≤ Real.log A + (n : ℝ) * Real.log d
    linarith
  · have hMp : 0 < M := by linarith
    have hq := Real.log_le_sub_one_of_pos (div_pos hMp hd)
    rw [Real.log_div hMp.ne' hd.ne'] at hq
    have hmul := mul_le_mul_of_nonneg_left hq hn
    have hfrac : (n : ℝ) * (M / d) ≤ M := by
      have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
      have hqp : 0 ≤ M / d := div_nonneg hM hd.le
      dsimp [d] at hcancel
      nlinarith [mul_nonneg hn hqp]
    rw [max_eq_left (le_of_not_ge hs)]
    change Real.log A + (n : ℝ) * Real.log M - M ≤ Real.log A + (n : ℝ) * Real.log d
    nlinarith
