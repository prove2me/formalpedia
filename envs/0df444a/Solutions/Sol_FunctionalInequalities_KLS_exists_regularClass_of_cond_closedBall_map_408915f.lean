-- Prove2me | solution 1 for FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:27:45.517593+00:00
-- url     : https://prove2.me/submissions/2de38287-a04e-4ba1-b51f-44b3fcb4b43f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
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
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_law_comp_affine_408915f

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
variable {V : E → ℝ} {a b : ℝ}
/-- The normalizing constant is positive. -/
theorem FunctionalInequalities.KLS.RegularPotential.integral_exp_neg_pos (hV : RegularPotential V a b) :
    0 < ∫ x, Real.exp ((-V) x) ∂(volume : Measure E) := by
    apply integral_exp_pos
    exact integrable_exp_neg hV
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end
end

noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
private theorem FunctionalInequalities.KLS.letwin_cond_map_equiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A ≃ᵐ B) (S : Set A) (hS : MeasurableSet S) :
    (ProbabilityTheory.cond μ S).map e =
      ProbabilityTheory.cond (μ.map e) (e '' S) := by
  have hpre : e ⁻¹' (e '' S) = S :=
    Set.preimage_image_eq S e.injective
  have hm : (μ.map e) (e '' S) = μ S := by
    rw [Measure.map_apply e.measurable (e.measurableSet_image.mpr hS), hpre]
  rw [ProbabilityTheory.cond, Measure.map_smul, ProbabilityTheory.cond, hm,
    e.measurableEmbedding.restrict_map, hpre]
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.KLS.letwin_cond_density
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b)
    (S : Set E) (hS : MeasurableSet S) (h0 : (hV.law : Measure E) S ≠ 0) :
    ProbabilityTheory.cond (hV.law : Measure E) S =
      volume.withDensity
        (S.indicator fun x =>
          ENNReal.ofReal
            (Real.exp
              (-(V x + Real.log
                ((∫ y, Real.exp (-V y) ∂(volume : Measure E)) *
                  ((hV.law : Measure E) S).toReal))))) := by
  let Z : ℝ := ∫ x, Real.exp (-V x) ∂(volume : Measure E)
  let m : ℝ := ((hV.law : Measure E) S).toReal
  have hZ : 0 < Z := hV.integral_exp_neg_pos
  have hm : 0 < m :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have hi : ENNReal.ofReal m⁻¹ = ((hV.law : Measure E) S)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hm,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hd : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x) / Z)) :=
    (hV.temperate.1.continuous.neg.measurable.exp.div_const Z).ennreal_ofReal
  change
    ((hV.law : Measure E) S)⁻¹ •
      ((volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-V x) / Z))).restrict S) = _
  rw [restrict_withDensity hS, ← withDensity_smul _ hd, withDensity_indicator hS]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change
    ((hV.law : Measure E) S)⁻¹ * ENNReal.ofReal (Real.exp (-V x) / Z) =
      ENNReal.ofReal (Real.exp (-(V x + Real.log (Z * m))))
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Z * m)),
    Real.exp_log (mul_pos hZ hm)]
  have he :
      Real.exp (-V x) * (Z * m)⁻¹ =
        m⁻¹ * (Real.exp (-V x) / Z) := by
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), hi]
private theorem FunctionalInequalities.KLS.letwin_convex_sub_quadratic
    {f : E → ℝ} {a : ℝ} (hf : ContDiff ℝ 2 f)
    (h : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ f x v v) :
    ConvexOn ℝ univ (fun y => f y - (a / 2) * ‖y‖ ^ 2) := by
  have hc : ConvexOn ℝ univ (fun y => f y + (-a) / 2 * ‖y‖ ^ 2) := by
    apply Analysis.BakryEmery.convexOn_of_hessian_ge_408915f
      (hf.add (contDiff_const.mul (contDiff_norm_sq ℝ))) (ρ := 0) le_rfl
    intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic hf]
    have hh := h x v
    nlinarith
  simpa only [neg_div, neg_mul, ← sub_eq_add_neg] using hc
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities.KLS in
/-- **Ball-conditioned, affinely transported regular laws lie in Letwin's class** (Letwin Lemma A.1):
conditioning the law of a regular potential `V` on `closedBall 0 R` (`R > 0`) and pushing forward by
`x ↦ L (x − c)` gives `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and uniformly
convex. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b) {R : ℝ} (hR : 0 < R) (L : E ≃L[ℝ] E)
    (c : E) :
    ∃ (K : Set E) (W : E → ℝ) (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      ContDiff ℝ ∞ W ∧ ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
      (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map (fun x => L (x - c)) =
        (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
  let H : E ≃ₜ E := (Homeomorph.addRight (-c)).trans L.toHomeomorph
  let e : E ≃ᵐ E := H.toMeasurableEquiv
  let K : Set E := e '' closedBall (0 : E) R
  have he : (e : E → E) = fun x => L (x - c) := by
    funext x
    change L (x + -c) = L (x - c)
    rw [sub_eq_add_neg]
  have hKcompact : IsCompact K := by
    change IsCompact (H '' closedBall (0 : E) R)
    exact (isCompact_closedBall (0 : E) R).image H.continuous
  have hKconvex : Convex ℝ K := by
    have heq :
        K = L '' ((fun x => -c + x) '' closedBall (0 : E) R) := by
      change e '' closedBall (0 : E) R =
        L '' ((fun x => -c + x) '' closedBall (0 : E) R)
      rw [Set.image_image]
      congr 1
      funext x
      rw [he]
      change L (x - c) = L (-c + x)
      rw [sub_eq_add_neg, add_comm]
    rw [heq]
    exact ((convex_closedBall (0 : E) R).translate (-c)).linear_image
      (L : E →ₗ[ℝ] E)
  have hKinterior : (interior K).Nonempty := by
    change (interior (H '' closedBall (0 : E) R)).Nonempty
    rw [← H.image_interior]
    exact ⟨H 0, Set.mem_image_of_mem H
      (mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds (0 : E) hR))⟩
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  let U : E → ℝ := fun y => V (L.symm y + c)
  let κ : ℝ := FunctionalInequalities.KLS.RegularPotential.affineLowerConstant a L.symm
  have hU : FunctionalInequalities.KLS.RegularPotential U κ
      (FunctionalInequalities.KLS.RegularPotential.affineUpperConstant b L.symm) :=
    hV.comp_affine L.symm c
  have hmap : (hV.law : Measure E).map e = (hU.law : Measure E) := by
    rw [he]
    simpa only [ContinuousLinearEquiv.symm_symm] using
      (hV.law_comp_affine_408915f L.symm c).symm
  have hK0 : (hU.law : Measure E) K ≠ 0 := by
    obtain ⟨y, hy⟩ := hKinterior
    have hpos : 0 < (volume : Measure E) K :=
      Measure.measure_pos_of_mem_nhds volume (mem_interior_iff_mem_nhds.mp hy)
    intro hz
    exact (ne_of_gt hpos) (absolutelyContinuous_tilted hU.integrable_exp_neg hz)
  let d : ℝ :=
    Real.log
      ((∫ y, Real.exp (-U y) ∂(volume : Measure E)) *
        ((hU.law : Measure E) K).toReal)
  let W : E → ℝ := fun y => U y + d
  have hW : ContDiff ℝ ∞ W := hU.temperate.1.add contDiff_const
  have hconv : ConvexOn ℝ univ (fun y => U y - (κ / 2) * ‖y‖ ^ 2) :=
    letwin_convex_sub_quadratic
      (hU.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hU.lower
  have hWconv : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) := by
    have hh := hconv.add_const d
    change ConvexOn ℝ univ (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) at hh
    have heq :
        (fun y => W y - (κ / 2) * ‖y‖ ^ 2) =
          (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) := by
      funext y
      dsimp only [W]
      ring
    rw [heq]
    exact hh
  refine ⟨K, W, κ, hU.pos, hKcompact, hKconvex, hKinterior, hW, hWconv, ?_⟩
  calc
    (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map
        (fun x => L (x - c)) =
      (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map e := by
        rw [he]
    _ = ProbabilityTheory.cond ((hV.law : Measure E).map e) K :=
      letwin_cond_map_equiv (hV.law : Measure E) e
        (closedBall (0 : E) R) measurableSet_closedBall
    _ = ProbabilityTheory.cond (hU.law : Measure E) K := by rw [hmap]
    _ = (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) :=
      letwin_cond_density hU K hKmeas hK0
