-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:39:44.946508+00:00
-- url     : https://prove2.me/submissions/ddf1b69a-fcdb-4d9d-9efd-da804dcddbdc

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
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_ae_add_eq_of_integral_mul_fderiv_eq_zero_408915f
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_restrict_le_smul_of_eq_tilted_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Translation invariance up to null sets passes to the measurable representative. -/
theorem FunctionalInequalities.Energy.Euclidean.forall_ae_add_eq_mk {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) (v : V) :
    ∀ᵐ x ∂m, hh.mk h (x + v) = hh.mk h x := by
  have hmk : ∀ᵐ x ∂m, h (x + v) = hh.mk h (x + v) :=
    (measurePreserving_add_right m v).quasiMeasurePreserving.ae hh.ae_eq_mk
  filter_upwards [hmk, htr v, hh.ae_eq_mk] with x hx₁ hx₂ hx₃
  exact hx₁.symm.trans (hx₂.trans hx₃)
/-- A function invariant under every translation up to null sets is almost everywhere constant. -/
theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_forall_ae_add_eq {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  obtain ⟨c, hc⟩ :=
    exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f m
      hh.measurable_mk (forall_ae_add_eq_mk m hh htr)
  refine ⟨c, ?_⟩
  filter_upwards [hh.ae_eq_mk, hc] with x hx₁ hx₂
  exact hx₁.trans hx₂
/-- **Zero weak gradient implies constancy**: a locally integrable `h` with
`∫ h ∂_w φ dm = 0` for all `φ ∈ C_c^∞` and all `w` is `m`-almost everywhere constant. -/
theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  exact exists_ae_eq_const_of_forall_ae_add_eq m hh.aestronglyMeasurable
    (fun v => ae_add_eq_of_integral_mul_fderiv_eq_zero_408915f m hh h0 v)
end
end
end
end
end

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
/-- Every `L²(ν)` class is locally integrable for Haar measure. -/
theorem FunctionalInequalities.KLS.LogConcave.locallyIntegrable_coeFn (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    (f : Lp ℝ 2 (ν : Measure V)) : LocallyIntegrable (f : V → ℝ) m := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨c, hc, hle⟩ := restrict_le_smul_of_eq_tilted_408915f m hνU hU hK
  have h1 : Integrable (f : V → ℝ) (ν : Measure V) :=
    (Lp.memLp f).integrable (by norm_num)
  exact (h1.smul_measure hc).mono_measure hle
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **The kernel of the closed unit gradient consists of constants**: if `T̄ h = 0`, then `h` is the
`L²(ν)` constant equal to its mean. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) :
    (h : Lp ℝ 2 (ν : Measure V)) = FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by
  obtain ⟨c, hc⟩ :=
    FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero m
      (FunctionalInequalities.KLS.LogConcave.locallyIntegrable_coeFn m hνU hU (h : Lp ℝ 2 (ν : Measure V)))
      (fun φ hφ hφc w =>
        FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_408915f
          m hν hi hνU hU h h0 hφ hφc w)
  have hac : (ν : Measure V) ≪ m := by
    rw [hνU]
    exact tilted_absolutelyContinuous m (-U)
  have hae :
      (h : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    hac.ae_le hc
  have hconst :
      (FunctionalInequalities.L2.const ν c : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    FunctionalInequalities.L2.const_coeFn ν c
  have hL :
      (h : Lp ℝ 2 (ν : Measure V)) = FunctionalInequalities.L2.const ν c :=
    Lp.ext (hae.trans hconst.symm)
  rw [hL, FunctionalInequalities.L2.mean_const]
