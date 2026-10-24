-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_potential_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:59.307515+00:00
-- url     : https://prove2.me/submissions/6e705119-14a8-4c2e-8de5-4c08465fd1e1

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_map_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_eventually_abs_sub_quadratic_le_of_subgradient_expansion_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_gradient_of_second_difference_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_posDef_and_det_eq_of_quadratic_expansion_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_map_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_eq_lintegral_of_isOpen_408915f
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_momentMap_aux_408915f

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end
end
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Probability.Stein.hessianMatrix_entry_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) (i j : Fin n) :
    hessianMatrix u x i j =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [hessian_symm_of_gradient_diff hu hx,
    ← hessian_coord_of_gradient_diff hx]
  have heq :
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        fun y => ⟪gradient u y, EuclideanSpace.basisFun (Fin n) ℝ i⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [heq, fderiv_inner_apply ℝ hx
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp [real_inner_comm]
/-- At a point where the gradient of a `C¹` potential is differentiable, its derivative
is represented by the coordinate Hessian. This pointwise bridge requires no `C²` hypothesis
and supports the weak regular moment-potential package for Letwin's Lemma 2.2. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  exact hessianMatrix_entry_of_differentiableAt_gradient hu hx i j
/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx
end
end
end
end GradientDerivativeIdentification
end

section
noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- **`C^{1,1}` regularity of the moment potential** (weak Letwin route; KLS500
`weak_moment_mollify_hessian_upper`/`moment gradient Lipschitz`): if the `C¹` convex Lipschitz `u` with
`∫ e^{-u} = 1` pushes `e^{-u} dx` forward by `∇u` to `1_K e^{-V} dx` with `K` compact convex and `V ∈ C¹` such
that `V − (κ/2)‖·‖²` is convex, then `∇u` is `16/κ`-Lipschitz. -/
theorem FunctionalInequalities.Analysis.lipschitzWith_gradient_of_map_gradient {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) := by
  have hsd := secondDifference_le_of_map_gradient_408915f hu hconv hnorm hK hKc hV hκ hstrong hmap hC1
  have hLip :=
    lipschitzWith_gradient_of_second_difference_le_408915f hconv
      (hC1.differentiable (by norm_num)) (show 0 ≤ 4 / κ by positivity) hsd
  have hconstant : 4 * (4 / κ) = 16 / κ := by ring
  rw [hconstant] at hLip
  exact hLip
end
end
end
end

section
noncomputable section
open MeasureTheory Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation; weak Letwin route): for an isotropic probability law `μ` supported in the closed
ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1` whose a.e.
gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is claimed. -/
theorem FunctionalInequalities.KLS.CEK.exists_momentMap_of_isotropic_of_ae_norm_le (μ : ProbabilityMeasure E)
    (hμ : KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = (μ : Measure E) := by
  exact exists_momentMap_aux_408915f μ hμ L hL
end
end
end
end
end

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
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
/-- A regular-class isotropic law has a convex Lipschitz C1 moment potential with
16/kappa-Lipschitz gradient and the a.e. Hessian/log-det package. -/
theorem solution {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial E := inferInstance
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  let L : NNReal := ⟨R, hR.le⟩
  have hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ) := by
    rw [hμ]
    refine (ae_withDensity_iff ?_).2 ?_
    · exact Measurable.indicator
        (Measurable.ennreal_ofReal
          (Real.continuous_exp.measurable.comp
            (Measurable.neg hW.continuous.measurable)))
        hK.measurableSet
    · filter_upwards [] with y hy
      by_cases hyK : y ∈ K
      · exact hRK y hyK
      · rw [Set.indicator_of_notMem hyK] at hy
        exact (hy rfl).elim
  obtain ⟨u, huconv, huLip, hunorm, humap⟩ :=
    FunctionalInequalities.KLS.CEK.exists_momentMap_of_isotropic_of_ae_norm_le μ hiso L hL
  have hmap :
      ((volume : Measure E).tilted (-u)).map (gradient u) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) :=
    humap.trans hμ
  have huC1 : ContDiff ℝ 1 u :=
    FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_408915f huLip huconv hunorm hK hKc hKint
      hW.continuous hmap
  have hgradLip : LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) :=
    FunctionalInequalities.Analysis.lipschitzWith_gradient_of_map_gradient huLip huconv hunorm hK hKc
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hκ hstrong hmap huC1
  let f : E → ℝ := fun x => Real.exp (-u x + W (gradient u x))
  have hgradc : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (huC1.continuous_fderiv (by norm_num))
  have hf : Continuous f :=
    Real.continuous_exp.comp
      (huC1.continuous.neg.add (hW.continuous.comp hgradc))
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hMA : ∀ G : Set E, IsOpen G →
      volume (FunctionalInequalities.Analysis.subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) := by
    intro G hG
    exact FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f huLip huconv hunorm
      hK.isClosed hKc hW.continuous.measurable hmap hG
  have hdiff :
      ∀ᵐ x ∂(volume : Measure E), DifferentiableAt ℝ (gradient u) x :=
    hgradLip.ae_differentiableAt
  have hmain :
      ∀ᵐ x ∂(volume : Measure E),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
          Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) := by
    filter_upwards [hdiff] with x hx
    let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
    have hT : HasFDerivAt (gradient u) T x := hx.hasFDerivAt
    have hfd : ∀ y, HasFDerivAt u (fderiv ℝ u y) y :=
      fun y => (huC1.differentiable (by norm_num) y).hasFDerivAt
    have hsub (y q : E)
        (hq : ∀ w, u y + ⟪q, w - y⟫ ≤ u w) :
        q = gradient u y := by
      have hm : IsLocalMin (fun z => u z -
          (InnerProductSpace.toDual ℝ E q) z) y := by
        filter_upwards [] with z
        change u y - (InnerProductSpace.toDual ℝ E q) y ≤
          u z - (InnerProductSpace.toDual ℝ E q) z
        simp only [InnerProductSpace.toDual_apply_apply]
        have hz := hq z
        rw [inner_sub_right] at hz
        linarith
      have hz := hm.hasFDerivAt_eq_zero
        ((hfd y).sub (InnerProductSpace.toDual ℝ E q).hasFDerivAt)
      have hdu :
          fderiv ℝ u y =
            (InnerProductSpace.toDual ℝ E) (gradient u y) :=
        (toDual_gradient (f := u) (x := y)).symm
      rw [hdu] at hz
      exact ((InnerProductSpace.toDual ℝ E).injective
        (sub_eq_zero.mp hz)).symm
    have hexp :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E,
          (∀ w, u y + ⟪q, w - y⟫ ≤ u w) →
            ‖q - gradient u x - T (y - x)‖ ≤ ε * ‖y - x‖ := by
      intro ε hε
      have hlittle := hT.isLittleO
      filter_upwards [hlittle.bound hε] with y hy q hq
      have hqeq := hsub y q hq
      simpa only [hqeq] using hy
    have hquad :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - u x - ⟪gradient u x, y - x⟫ -
              1 / 2 * ⟪T (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 :=
      fun ε hε =>
        FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_408915f
          huconv hexp ε hε
    have hmat := FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hx
    have hquad' :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - FunctionalInequalities.Analysis.quadraticAt (FunctionalInequalities.Probability.Stein.hessianMatrix u x) x
              (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
      intro ε hε
      filter_upwards [hquad ε hε] with y hy
      rw [FunctionalInequalities.Analysis.quadraticAt, hmat]
      change
        |u y - (u x + ⟪gradient u x, y - x⟫ +
          1 / 2 * ⟪y - x, T (y - x)⟫)| ≤ ε * ‖y - x‖ ^ 2
      rw [real_inner_comm (T (y - x)) (y - x)]
      simpa only [sub_add_eq_sub_sub] using hy
    have hres := FunctionalInequalities.Analysis.posDef_and_det_eq_of_quadratic_expansion_408915f huconv
      isOpen_univ (fun G hG _ => hMA G hG) (mem_univ x)
      hf.continuousAt (hfpos x)
      (FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hx) hquad'
    refine ⟨hres.1, ?_⟩
    calc
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.log (f x) := by
        rw [hres.2]
      _ = -u x + W (gradient u x) := by
        simp [f]
  refine ⟨u, L, huconv, huLip, hunorm, humap, huC1, hgradLip, ?_⟩
  filter_upwards [hmain, hdiff] with x hx hxd
  refine ⟨hx.1, hx.2, ?_⟩
  let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
  have hTnorm : ‖T‖ ≤ 16 / κ := by
    have h := norm_fderiv_le_of_lipschitz ℝ hgradLip (x₀ := x)
    have hc : (0 : ℝ) ≤ 16 / κ := by positivity
    rw [Real.coe_toNNReal (16 / κ) hc] at h
    exact h
  have hmat := FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hxd
  have hH : (FunctionalInequalities.Probability.Stein.hessianMatrix u x).IsHermitian :=
    FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hxd
  have hsym : T.toLinearMap.IsSymmetric := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    rw [hmat] at hs
    exact hs
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hone :
      Matrix.toLin b.toBasis b.toBasis
          (1 : Matrix (Fin n) (Fin n) ℝ) =
        LinearMap.id :=
    Matrix.toLin_one _
  have hop :
      Matrix.toEuclideanLin
          ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
            FunctionalInequalities.Probability.Stein.hessianMatrix u x) =
        (16 / κ) • LinearMap.id - T.toLinearMap := by
    have hmat' := hmat
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at hmat'
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, map_sub, map_smul, hone, hmat']
  rw [← Matrix.isPositive_toEuclideanLin_iff, hop]
  constructor
  · intro v w
    change
      ⟪(16 / κ) • v - T v, w⟫ =
        ⟪v, (16 / κ) • w - T w⟫
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    have hsw : ⟪T v, w⟫ = ⟪v, T w⟫ := hsym v w
    rw [hsw]
  · intro v
    change 0 ≤ ⟪(16 / κ) • v - T v, v⟫
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hv := T.le_opNorm v
    have hv' : ‖T v‖ ≤ (16 / κ) * ‖v‖ :=
      hv.trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg v))
    have hi := real_inner_le_norm (T v) v
    have hq := mul_le_mul_of_nonneg_right hv' (norm_nonneg v)
    nlinarith
