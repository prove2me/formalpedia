-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:28:01.068317+00:00
-- url     : https://prove2.me/submissions/c3265342-0ef9-45ea-9e60-d070953e69e8

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
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- Elementary logarithmic coercivity. The bound is constructed from A,n,b;
no asymptotic growth or desired integral bound is passed as a premise. -/
theorem solution (A : ℝ) (n : ℕ) (b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 0 ≤ M →
      b ≤ Real.log A + (n : ℝ) * Real.log (max M 1) - M → M ≤ B := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < d := by dsimp [d]; positivity
  let B : ℝ := max 1 (2 * (Real.log A + (n : ℝ) * Real.log d - b))
  refine ⟨B, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro M hM hb
  by_cases hsmall : M ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hMpos : 0 < M := by linarith
  have hq := Real.log_le_sub_one_of_pos (div_pos hMpos hd)
  rw [Real.log_div hMpos.ne' hd.ne'] at hq
  have hmul := mul_le_mul_of_nonneg_left hq hn
  have hfraction : (n : ℝ) * (M / d) ≤ M / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
    have hqpos : 0 ≤ M / d := div_nonneg hM hd.le
    dsimp [d] at hcancel
    nlinarith
  rw [max_eq_left (le_of_not_ge hsmall)] at hb
  have hB : M ≤ 2 * (Real.log A + (n : ℝ) * Real.log d - b) := by nlinarith
  exact hB.trans (le_max_right _ _)
