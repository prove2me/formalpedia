-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:03.964888+00:00
-- url     : https://prove2.me/submissions/c6aea6fb-dd68-4d76-b783-7bde20d471fb

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
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Nonnegativity plus the actual linear lower bound controls the density after
scaling by max(M,1). This is where the small-integral protection is used. -/
theorem solution (φ : E → EReal) {c C M a : ℝ}
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
    (hlower : ∀ y, 0 ≤ FunctionalInequalities.Analysis.legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ y)
    (y : E) : FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖)) := by
  have hb : ((c * ‖y‖ - C : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ (a • y) := by
    by_cases h : c * ‖y‖ - C ≤ 0
    · exact (EReal.coe_nonpos.mpr h).trans (hlower (a • y)).1
    · have hpos : 0 ≤ c * ‖y‖ - C := (lt_of_not_ge h).le
      have hs := mul_le_mul_of_nonneg_right ha hpos
      have hm := mul_le_mul_of_nonneg_left hMa hC
      have hnorm : ‖a • y‖ = a * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ a)]
      apply (EReal.coe_le_coe_iff.mpr (show c * ‖y‖ - C ≤ c * ‖a • y‖ - C * M by
        rw [hnorm]
        nlinarith)).trans (hlower (a • y)).2
  have he := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hb)
  simpa only [FunctionalInequalities.Probability.MomentMeasure.density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using he
