-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:12:56.813477+00:00
-- url     : https://prove2.me/submissions/b940178b-38c2-47c1-9003-efe2ab9f66d0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
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
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_cumulant_compactPosterior_408915f

section
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
private theorem FunctionalInequalities.Analysis.directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp
/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem FunctionalInequalities.Analysis.directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) : directional (u :: t :: hs) f x = directional [u,t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) v w
/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem FunctionalInequalities.Analysis.directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
/-- Raw real C∞ iterated derivatives are symmetric under every slot permutation. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_perm {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (h : Fin m → E) (σ : Equiv.Perm (Fin m)) (x : E) :
    iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h := by
  rw [← directional_ofFn hf, ← directional_ofFn hf]
  exact congrFun (directional_perm hf (σ.ofFn_comp_perm h)) x
end
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
section
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
private theorem FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_param_slice
    {n : ℕ} (ψ : Param n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ψ (y, Q)) c h =
      iteratedFDeriv ℝ m ψ (c, Q)
        (fun i => (h i, (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let K := E →L[ℝ] E
  let L : E →L[ℝ] E × K := ContinuousLinearMap.inl ℝ E K
  let a : E × K := (0, Q)
  let g : E × K → ℝ := fun z => ψ (z + a)
  have hg : ContDiff ℝ ∞ g := by
    exact hψ.comp
      (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ (fun _ : E × K => a)))
  have hm_top : (m : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr le_top
  have hcomp :=
    L.iteratedFDeriv_comp_right hg c (i := m) hm_top
  have hshift :
      iteratedFDeriv ℝ m g (L c) =
        iteratedFDeriv ℝ m ψ (L c + a) := by
    simpa [g] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) m a (L c))
  have hcomp' := congrArg (fun T => T h) hcomp
  rw [hshift] at hcomp'
  simpa [E, K, L, a, g, Function.comp_def,
    ContinuousLinearMap.inl_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hcomp'
private theorem FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_cons_eq_snoc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {m : ℕ}
    (hf : ContDiff ℝ ∞ f) (h : Fin m → E) (v : E) :
    iteratedFDeriv ℝ (m + 1) f x (Fin.cons v h) =
      iteratedFDeriv ℝ (m + 1) f x (Fin.snoc h v) := by
  have hperm :
      (Fin.snoc h v) ∘ ⇑(FunctionalInequalities.KLS.BKL.Localization.snocToCons m) = Fin.cons v h := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [FunctionalInequalities.KLS.BKL.Localization.snocToCons]
    · simp [FunctionalInequalities.KLS.BKL.Localization.snocToCons]
  have hp :=
    FunctionalInequalities.Analysis.iteratedFDeriv_perm
      hf (m + 1) (Fin.snoc h v) (FunctionalInequalities.KLS.BKL.Localization.snocToCons m) x
  rw [hperm] at hp
  exact hp
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities.KLS.BKL.Localization in
/-- **The `c`-derivative of a cumulant is the next cumulant**: `D_c κ_m(h)[v] = κ_{m+1}(h, v)` (BKL p. 20,
`∇ᵐv_t(0) = κ_{m+1}`; the noise of (67) only moves `c`). -/
theorem solution {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n))
    (p : FunctionalInequalities.KLS.BKL.Localization.Param n) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
        FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p (v, 0) =
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v) := by
  let ψ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2
  let U : Fin m → FunctionalInequalities.KLS.BKL.Localization.Param n := fun i => (h i, 0)
  have hψ : ContDiff ℝ ∞ ψ := by
    simpa [ψ] using FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_408915f μ hc
  have hcum :
      (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
        FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n))) m h) =
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) := by
    funext q
    calc
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n))) m h =
          iteratedFDeriv ℝ m (fun y =>
            FunctionalInequalities.Probability.Posterior.logPartition μ y q.2) q.1 h :=
        congrArg (fun T => T h) (FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_408915f μ hc q.1 q.2 hm)
      _ = (iteratedFDeriv ℝ m ψ q) U := by
        simpa [ψ, U] using
          iteratedFDeriv_param_slice ψ hψ h q.1 q.2
  rw [hcum]
  have hdiff :
      Differentiable ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => iteratedFDeriv ℝ m ψ q) :=
    hψ.differentiable_iteratedFDeriv
      (m := m) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))
  let w : FunctionalInequalities.KLS.BKL.Localization.Param n := (v, 0)
  let Ulast : Fin (m + 1) → FunctionalInequalities.KLS.BKL.Localization.Param n := Fin.snoc U w
  have hderiv :
      fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
        iteratedFDeriv ℝ (m + 1) ψ p Ulast := by
    calc
      fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
          (fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => iteratedFDeriv ℝ m ψ q) p (v, 0)) U :=
        fderiv_continuousMultilinear_apply_const_apply
          hdiff.differentiableAt U (v, 0)
      _ = iteratedFDeriv ℝ (m + 1) ψ p (Fin.cons w U) := by
        simpa [w] using
          (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := ψ) (x := p)
            (Fin.cons w U)).symm
      _ = iteratedFDeriv ℝ (m + 1) ψ p Ulast :=
        iteratedFDeriv_cons_eq_snoc hψ U w
  rw [hderiv]
  let hv : Fin (m + 1) → EuclideanSpace ℝ (Fin n) := Fin.snoc h v
  have hU : (fun i : Fin (m + 1) => ((hv i, 0) : FunctionalInequalities.KLS.BKL.Localization.Param n)) = Ulast := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hv, Ulast, w]
    · simp [hv, Ulast, U]
  have hs := iteratedFDeriv_param_slice ψ hψ hv p.1 p.2
  rw [hU] at hs
  calc
    iteratedFDeriv ℝ (m + 1) ψ p Ulast =
        iteratedFDeriv ℝ (m + 1)
          (fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) p.1 (Fin.snoc h v) := by
      simpa [ψ, hv] using hs.symm
    _ = FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 :
        Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v) := by
      have hcumulant :=
        FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_408915f μ hc p.1 p.2
          (hm := Nat.succ_le_succ (Nat.zero_le m))
      exact (congrArg (fun T => T (Fin.snoc h v)) hcumulant).symm
