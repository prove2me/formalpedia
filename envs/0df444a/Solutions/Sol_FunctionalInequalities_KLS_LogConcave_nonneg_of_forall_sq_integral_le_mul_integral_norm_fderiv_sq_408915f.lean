-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:35:19.527964+00:00
-- url     : https://prove2.me/submissions/9cf1be35-5c5b-48d7-b66e-a3cc831f26f1

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
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
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory
open scoped ContDiff
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
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **A dual gradient bound has a nonnegative constant** (support for the `H⁻¹` variance lemma,
Letwin arXiv:2607.24164v1, Proposition 2.8): if `ν = e^{-W} dm` with `W` continuous on
`EuclideanSpace ℝ (Fin n)`, `n ≥ 1`, and `(∫ F h dν)² ≤ K ∫ ‖∇h‖² dν` for every `h ∈ C_c^∞`, then
`0 ≤ K` (some test has `∫ ‖∇h‖² dν > 0 because the density is positive). -/
theorem solution {n : ℕ} (hn : 0 < n)
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : Continuous W) {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, F x * h x ∂(ν : Measure _)) ^ 2 ≤
        K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    0 ≤ K := by
  by_contra hK'
  have hKneg : K < 0 := lt_of_not_ge hK'
  let Z : ℝ := ∫ x, Real.exp (-W x) ∂m
  have hZne : Z ≠ 0 := by
    intro hZ
    have hUniv := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ) hνW
    simp [Measure.tilted, Z, hZ] at hUniv
  have hZpos : 0 < Z := by
    have hZnonneg : 0 ≤ Z := by
      exact integral_nonneg (fun x => Real.exp_nonneg (-W x))
    exact lt_of_le_of_ne hZnonneg hZne.symm
  have hνopen :
      ∀ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U → U.Nonempty →
        (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    intro U hUopen hUnonempty
    rw [hνW]
    change
      (m.withDensity
          (fun x => ENNReal.ofReal (Real.exp ((-W) x) / Z))) U ≠ 0
    have hcontden :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) := by
      exact
        ENNReal.continuous_ofReal.comp
          ((Real.continuous_exp.comp hW.neg).div_const Z)
    have haeden :
        AEMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) m :=
      hcontden.aemeasurable
    have hset :
        {x : EuclideanSpace ℝ (Fin n) |
            ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} = Set.univ := by
      ext x
      change ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0 ↔ True
      exact iff_true_intro
        (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) hZpos)))
    intro hzero
    have hmzero :
        m
            ({x : EuclideanSpace ℝ (Fin n) |
                ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} ∩ U) = 0 :=
      (withDensity_apply_eq_zero' haeden).mp hzero
    have hmzeroU : m U = 0 := by
      rw [← Set.univ_inter U, ← hset]
      exact hmzero
    exact (Measure.IsOpenPosMeasure.open_pos U hUopen hUnonempty) hmzeroU
  let c : EuclideanSpace ℝ (Fin n) := 0
  let φ : ContDiffBump c := ⟨1, 2, by norm_num, by norm_num⟩
  let i : Fin n := ⟨0, hn⟩
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  let h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => φ x * (L x - L c)
  have hcφ : (φ c : ℝ) = 1 := by
    apply φ.one_of_mem_closedBall
    simpa [Metric.mem_closedBall] using φ.rIn_pos.le
  have hφdiff : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) :=
    φ.contDiff
  have hφ :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ))
        (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) c) c := by
    exact ((hφdiff.differentiable (by simp)) c).hasFDerivAt
  have hL :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => L x - L c) L c := by
    simpa using L.hasFDerivAt.sub_const (L c)
  have hh : HasFDerivAt h L c := by
    change HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ) * (L x - L c)) L c
    have hm := hφ.mul hL
    rw [hcφ, sub_self, one_smul, zero_smul, add_zero] at hm
    exact hm
  have hcont : ContDiff ℝ ∞ h := by
    exact hφdiff.mul (L.contDiff.sub contDiff_const)
  have hcomp : HasCompactSupport h := by
    exact φ.hasCompactSupport.mul_right
  have hLne : L ≠ 0 := by
    intro hLzero
    have hLzero' := congrArg
      (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        q (EuclideanSpace.single i 1)) hLzero
    simp [L] at hLzero'
  have hderivc : fderiv ℝ h c ≠ 0 := by
    rw [hh.fderiv]
    exact hLne
  have hfdcont : Continuous (fderiv ℝ h) := by
    exact hcont.continuous_fderiv (by simp)
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ‖fderiv ℝ h x‖ ^ 2
  have hgcont : Continuous g := by
    exact (continuous_norm.comp hfdcont).pow 2
  have hgcomp : HasCompactSupport g := by
    have hderivcomp : HasCompactSupport (fderiv ℝ h) := hcomp.fderiv ℝ
    apply hderivcomp.norm.mono
    intro x hx
    apply Function.mem_support.mpr
    intro hzero
    apply hx
    simp [g, hzero]
  have hgint : Integrable g (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact hgcont.integrable_of_hasCompactSupport hgcomp
  have hgpos : 0 < g c := by
    have hnorm : 0 < ‖fderiv ℝ h c‖ := norm_pos_iff.mpr hderivc
    exact sq_pos_of_pos hnorm
  let U : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < g x}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const hgcont
  have hcU : c ∈ U := by
    exact hgpos
  have hUzero : (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    exact hνopen U hUopen ⟨c, hcU⟩
  have hUpos : 0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) U :=
    pos_iff_ne_zero.mpr hUzero
  have hgsupp :
      0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) (Function.support g) := by
    apply lt_of_lt_of_le hUpos
    apply measure_mono
    intro x hx
    exact Function.mem_support.mpr (ne_of_gt hx)
  have henergy :
      0 < ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact
      (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hgint).mpr hgsupp
  have hineq := hK h hcont hcomp
  have hleft :
      0 ≤ (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 :=
    sq_nonneg _
  have hright :
      K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) < 0 :=
    mul_neg_of_neg_of_pos hKneg henergy
  have hcontra :
      (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 < 0 :=
    lt_of_le_of_lt hineq hright
  exact (not_lt_of_ge hleft) hcontra
