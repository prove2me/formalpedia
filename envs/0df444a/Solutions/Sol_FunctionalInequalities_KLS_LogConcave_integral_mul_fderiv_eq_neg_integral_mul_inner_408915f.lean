-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:37:08.182345+00:00
-- url     : https://prove2.me/submissions/220b221f-93ff-4b4f-ba6c-61c117238009

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_graph_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_inner_of_tendsto_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_of_tendsto_408915f

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
omit [SecondCountableTopology V] in
/-- Smooth integration by parts against a test: `∫ g ∂_w φ dm = -∫ φ ⟪∇g, w⟫ dm` for smooth `g`
and smooth compactly supported `φ`. -/
theorem FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_gradient {g φ : V → ℝ}
    (hg : ContDiff ℝ ∞ g) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, g x * fderiv ℝ φ x w ∂m = -∫ x, φ x * ⟪gradient g x, w⟫ ∂m := by
  have hIBP :=
    Energy.Euclidean.integral_mul_fderiv_apply m hφ hφc hg w
  have hgrad :
      (∫ x, φ x * ⟪gradient g x, w⟫ ∂m) =
        ∫ x, φ x * fderiv ℝ g x w ∂m := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Energy.Euclidean.inner_gradient_eq_fderiv_apply]
  linarith
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Weak gradient of an element of the closed domain**: for `h ∈ D(T̄)`, smooth compactly
supported `φ` and every direction `w`, `∫ h ∂_w φ dm = -∫ φ ⟪T̄ h, w⟫ dm`. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m =
      -∫ x, φ x * ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
        Lp V 2 (ν : Measure V)) x, w⟫ ∂m := by
  obtain ⟨g, hg, hgc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_graph_408915f m
      (ContinuousLinearMap.id ℝ V) hi h

  have hψ : Continuous (fun x => fderiv ℝ φ x w) := by
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

  have hψc : HasCompactSupport (fun x => fderiv ℝ φ x w) := by
    exact hφc.fderiv_apply ℝ w

  have hL :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (∫ x, (h : Lp ℝ 2 (ν : Measure V)) x *
          fderiv ℝ φ x w ∂m)) :=
    FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_408915f m hνU hU
      (fun n => FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n))
      h1 hψ hψc

  let G : ℕ → V → V :=
    fun n => FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g n)

  have hG : ∀ n, MemLp (G n) 2 (ν : Measure V) := by
    intro n
    dsimp [G]
    exact
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν
        (ContinuousLinearMap.id ℝ V) (hg n) (hgc n)).memLp_apply

  have h2' :
      Tendsto
        (fun n => (hG n).toLp (G n))
        atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h)) := by
    simpa [G] using h2

  have hR :
      Tendsto
        (fun n => ∫ x, φ x * ⟪G n x, w⟫ ∂m)
        atTop
        (𝓝 (∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto_408915f m hνU hU hG h2'
      hφ.continuous hφc w

  have hneg :
      Tendsto
        (fun n => -(∫ x, φ x * ⟪G n x, w⟫ ∂m))
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    hR.neg

  have heq :
      ∀ n, -(∫ x, φ x * ⟪G n x, w⟫ ∂m) =
        ∫ x, g n x * fderiv ℝ φ x w ∂m := by
    intro n
    simpa [G, FunctionalInequalities.Energy.WeightedGradient.apply_id] using
      (FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner_gradient
        m (hg n) hφ hφc w).symm

  have hL' :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) := by
    exact hneg.congr heq

  exact tendsto_nhds_unique hL hL'
