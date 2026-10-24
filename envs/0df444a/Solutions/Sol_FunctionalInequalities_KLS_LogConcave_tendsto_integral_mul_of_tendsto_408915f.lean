-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:33:03.674602+00:00
-- url     : https://prove2.me/submissions/8502413f-8454-480b-8b4d-8850a583563e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_eq_integral_mul_exp_408915f

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open Energy Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- `L²(ν)` convergence gives convergence of Haar integrals against a continuous compactly
supported weight. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {g : ℕ → V → ℝ} (hg : ∀ n, MemLp (g n) 2 (ν : Measure V))
    {f : Lp ℝ 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, g n x * ψ x ∂m) atTop (𝓝 (∫ x, f x * ψ x ∂m)) := by
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  let Ψ : V → ℝ := fun x => (Z * Real.exp (U x)) * ψ x

  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_408915f hνU

  have hΨcont : Continuous Ψ := by
    dsimp [Ψ]
    exact (continuous_const.mul (Real.continuous_exp.comp hU)).mul hψ

  have hsupport : Function.support Ψ ⊆ Function.support ψ := by
    intro x hx
    by_contra h
    have hψx : ψ x = 0 := by
      simpa [Function.mem_support] using h
    have hΨx : Ψ x = 0 := by
      simp [Ψ, hψx]
    exact hx hΨx

  have hΨc : HasCompactSupport Ψ := by
    exact hψc.mono hsupport

  have hΨ : MemLp Ψ 2 (ν : Measure V) :=
    hΨcont.memLp_of_hasCompactSupport hΨc

  have hpair :
      ∀ a : Lp ℝ 2 (ν : Measure V),
        (∫ x, (a : V → ℝ) x * Ψ x ∂(ν : Measure V)) =
          ⟪a, hΨ.toLp Ψ⟫ := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hΨ] with x hx
    rw [hx]
    exact mul_comm _ _

  have hseq :
      ∀ n, (∫ x, g n x * ψ x ∂m) =
        ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := by
    intro n
    calc
      ∫ x, g n x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * (g n x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_408915f m hνU (fun x => g n x * ψ x))
      _ = ∫ x, ((hg n).toLp (g n) : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [MemLp.coeFn_toLp (hg n)] with x hx
            dsimp [Ψ]
            rw [hx]
            ring
      _ = ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := hpair ((hg n).toLp (g n))

  have htarget :
      (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ := by
    calc
      ∫ x, f x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * ((f : V → ℝ) x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_408915f m hνU
                (fun x => (f : V → ℝ) x * ψ x))
      _ = ∫ x, (f : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [Ψ]
            ring
      _ = ⟪f, hΨ.toLp Ψ⟫ := hpair f

  have hinner :
      Tendsto
        (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫)
        atTop (𝓝 ⟪f, hΨ.toLp Ψ⟫) :=
    hlim.inner tendsto_const_nhds

  rw [show (fun n => ∫ x, g n x * ψ x ∂m) =
      (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫) from funext hseq]
  rw [show (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ from htarget]
  exact hinner
