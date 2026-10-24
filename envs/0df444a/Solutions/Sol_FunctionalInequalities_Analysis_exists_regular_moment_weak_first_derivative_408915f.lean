-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_weak_first_derivative_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:57:23.159141+00:00
-- url     : https://prove2.me/submissions/31e7a4db-3d35-4912-b594-cac87a604fa1

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_tensor_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_det_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Weak derivatives are unique almost everywhere. -/
theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e
end
end
universe u
end
end

section
noncomputable section
open scoped Matrix.Norms.Elementwise
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The determinant is differentiable (it is a continuous multilinear map of the rows). -/
theorem FunctionalInequalities.Analysis.differentiableAt_det (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M :=
  (FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).differentiableAt
end
end
section DeterminantPolynomialIdentification
open scoped BigOperators Matrix.Norms.Elementwise
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteIndex
variable {ι : Type*}
variable [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
/-- Derivative of the finite determinant polynomial along a scalar affine path.
No outer matrix chain rule, invertibility, or nonempty-index assumption. -/
private theorem FunctionalInequalities.Analysis.deriv_det_add_smul_zero
    (A N : Matrix ι ι ℝ) :
    deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hentry (σ : Equiv.Perm ι) (i : ι) :
      HasDerivAt (fun t : ℝ => A (σ i) i + t * N (σ i) i)
        (N (σ i) i) 0 := by
    simpa only [id_eq, one_mul] using
      HasDerivAt.const_add (A (σ i) i)
        ((hasDerivAt_id (0 : ℝ)).mul_const (N (σ i) i))
  have hprod (σ : Equiv.Perm ι) :
      HasDerivAt
        (fun t : ℝ => ∏ i : ι, (A (σ i) i + t * N (σ i) i))
        (∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simpa only [zero_mul, add_zero, smul_eq_mul, mul_comm] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (fun i _ => hentry σ i))
  have hpoly :
      HasDerivAt (fun t : ℝ => Matrix.det (A + t • N))
        (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : ι, N (σ i) i *
            ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact HasDerivAt.fun_sum
      (fun σ _ =>
        HasDerivAt.const_mul ((Equiv.Perm.sign σ : ℤ) : ℝ) (hprod σ))
  exact hpoly.deriv
/-- The signed permutation-polynomial determinant density is its existing
outer matrix derivative, including singular and empty matrices. -/
theorem FunctionalInequalities.Analysis.fderiv_det_eq_sum_permutation
    (A N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det A N =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hd : DifferentiableAt ℝ Matrix.det (A + (0 : ℝ) • N) := by
    simpa only [zero_smul, add_zero] using differentiableAt_det A
  calc
    fderiv ℝ Matrix.det A N =
        deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 := by
      simpa only [zero_smul, add_zero] using! hd.deriv_comp_add_smul.symm
    _ = _ := deriv_det_add_smul_zero A N
end FiniteIndex
end
end
end DeterminantPolynomialIdentification
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
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
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end
end
end HessianEntryBounds
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- The scalar exponential is Lipschitz on the half-line (-∞, C]; no lower
bound is required, and the threshold may be negative. -/
theorem FunctionalInequalities.Analysis.lipschitzOnWith_exp_Iic (C : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp C)) Real.exp (Set.Iic C) := by
  refine (convex_Iic C).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_
  intro x hx
  apply NNReal.coe_le_coe.mp
  change ‖Real.exp x‖ ≤ (Real.toNNReal (Real.exp C) : ℝ)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
    Real.coe_toNNReal _ (Real.exp_pos C).le]
  exact Real.exp_le_exp.mpr hx
end
end
end
end

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
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
open Matrix Metric
open scoped Matrix.Norms.Elementwise
/-- The actual normalized convex potential supplies an exponent upper bound.
No bound on F or minimum of u is assumed. -/
private theorem FunctionalInequalities.Analysis.exponent_upper_of_normalized_convex {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hconv : ConvexOn ℝ univ u) (hLip : LipschitzWith L u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hV : Continuous V) :
    ∃ C : ℝ, ∀ x, -u x + V (gradient u x) ≤ C := by
  have hint : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  obtain ⟨x₀, hx₀⟩ :=
    (exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
      volume hconv hint).1
  obtain ⟨D, hD⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).exists_bound_of_continuousOn
      hV.continuousOn
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hLip)
  refine ⟨D - u x₀, ?_⟩
  intro x
  have hg : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hgrad x
  have hv : V (gradient u x) ≤ D :=
    (le_abs_self (V (gradient u x))).trans (hD _ hg)
  linarith [hx₀ x]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The same actual-source moment potential and weak tensor retain all original
regularity data and satisfy the first weak Monge–Ampère identity (Letwin v1 (2.4)).
The determinant derivative is locally L2; the logarithmic weak derivative is
identified with the explicit source-law right-hand side. No C2 Hessian regularity
or prescribed derivative tensor is assumed. This does not prove the second
evolution identity, the integrated trace bound, or the constant-8 theorem. -/
theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  classical
  obtain ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG,
      hF, hw, hdata, hT⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor_408915f hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨C, hC⟩ := exponent_upper_of_normalized_convex hconv hLip hnorm hW.continuous
  have hmaps : MapsTo (fun x => -u x + W (gradient u x)) univ (Iic C) := by
    intro x _
    exact hC x
  have he : LipschitzWith (Real.toNNReal (Real.exp C) * LF)
      (fun x => Real.exp (-u x + W (gradient u x))) :=
    lipschitzOnWith_univ.mp ((FunctionalInequalities.Analysis.lipschitzOnWith_exp_Iic C).comp hF.lipschitzOnWith hmaps)
  refine ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT, ⟨_, he⟩, ?_⟩
  intro k
  have hbound (r s : Fin n) : MemLp (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x r s)
  have hp := FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_408915f
    (A := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x)
    (DA := fun x => Matrix.of fun i j => T x k i j)
    (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)
  have hchain :
      (fun x => fderiv ℝ (fun y => Real.exp (-u y + W (gradient u y))) x
        (EuclideanSpace.basisFun (Fin n) ℝ k)) =ᵐ[
          (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.exp (-u x + W (gradient u x)) *
        fderiv ℝ (fun y => -u y + W (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    filter_upwards [hF.ae_differentiableAt (μ := volume)] with x hx
    have h := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ k))
      hx.hasFDerivAt.exp.fderiv
    simpa only [_root_.smul_apply, smul_eq_mul] using h
  have hExpWeak := (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_408915f he
      (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae_408915f
        Filter.EventuallyEq.rfl hchain
  have hExpDet : (fun x => Real.exp (-u x + W (gradient u x))) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hDetExpWeak := hExpWeak.congr_ae_408915f hExpDet Filter.EventuallyEq.rfl
  have hDensity := hp.1.ae_eq hDetExpWeak
  have hW1 : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hAll :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : Fin n, T x k (σ i) i *
          ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, FunctionalInequalities.Probability.Stein.hessianMatrix u x (σ j) j) =
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace ∧
      ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
        fderiv ℝ (fun y => -u y + W (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
          ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) := by
    filter_upwards [hdata, hDensity, FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f hC1 hG hW1]
      with x hx hd hRight
    have hunit : IsUnit (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos)
    have hJ :
        (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : Fin n, T x k (σ i) i *
            ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, FunctionalInequalities.Probability.Stein.hessianMatrix u x (σ j) j) =
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace := by
      calc
        (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, FunctionalInequalities.Probability.Stein.hessianMatrix u x (σ j) j) =
            fderiv ℝ Matrix.det (FunctionalInequalities.Probability.Stein.hessianMatrix u x) (Matrix.of fun i j => T x k i j) :=
          (FunctionalInequalities.Analysis.fderiv_det_eq_sum_permutation (FunctionalInequalities.Probability.Stein.hessianMatrix u x) (Matrix.of fun i j => T x k i j)).symm
        _ = (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace :=
          FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_408915f _ _ hunit
    have hExpEq : (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
      rw [← hx.2.1, Real.exp_log hx.1.det_pos]
    have hTrace :
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
          fderiv ℝ (fun y => -u y + W (gradient u y)) x
            (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      apply mul_left_cancel₀ (ne_of_gt hx.1.det_pos)
      calc
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∑ i : Fin n, T x k (σ i) i *
                ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, FunctionalInequalities.Probability.Stein.hessianMatrix u x (σ j) j) := hJ.symm
        _ = Real.exp (-u x + W (gradient u x)) *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) := hd
        _ = (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) := by rw [hExpEq]
    exact ⟨hJ, hTrace, hTrace.trans (hRight k)⟩
  have hJac := hAll.mono fun _ hx => hx.1
  have hTrace :
      (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => fderiv ℝ (fun y => -u y + W (gradient u y)) x
        (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    hAll.mono fun _ hx => hx.2.1
  have hRight := hAll.mono fun _ hx => hx.2.2
  have hLog : (fun x => -u x + W (gradient u x)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det) :=
    hdata.mono fun _ hx => hx.2.1.symm
  have hLogWeak := (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_408915f hF
      (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae_408915f hLog hTrace.symm
  exact ⟨hp.1.congr_ae_408915f Filter.EventuallyEq.rfl hJac,
    fun S hS => MemLp.ae_eq (ae_restrict_of_ae hJac) (hp.2 S hS), hLogWeak, hTrace, hRight⟩
