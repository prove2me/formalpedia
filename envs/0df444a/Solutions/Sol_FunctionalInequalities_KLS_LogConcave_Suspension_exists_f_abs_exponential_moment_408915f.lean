-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:05:24.0852+00:00
-- url     : https://prove2.me/submissions/2aa0af43-59b9-4a0c-bb76-2a33cfa86d4f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_integrability_factorization_408915f

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
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
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Exponential moment of `f` from the joint law.** If the joint law has an exponential moment
`e^{r‖p‖}` and `N > 0`, then `f` has the exponential moment `e^{t|f|}` with
`t = r/(2σ_β√N)` (testing the factorization at `±(r/2) e_none`). -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => Real.exp (r * ‖p‖))
      (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x => Real.exp (t * |f x|)) μ := by
  let ν := FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  have hσ : 0 < FunctionalInequalities.KLS.LogConcave.Suspension.sigma β := by
    unfold FunctionalInequalities.KLS.LogConcave.Suspension.sigma
    apply Real.sqrt_pos.mpr
    positivity
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  let t := r / (2 * FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)
  have ht : 0 < t := div_pos hr (mul_pos (mul_pos (by norm_num) hσ) hroot)
  have hcoef : (r / 2) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) = t := by
    dsimp [t]
    rw [div_div]
    congr 1
    ring
  let e0 : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  let zp : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := (r / 2) • e0
  let zm : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := -zp
  have hhalf : 0 < r / 2 := by positivity
  have he0norm : ‖e0‖ = 1 :=
    (EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ).norm_eq_one none
  have hzp : ‖zp‖ ≤ r := by
    dsimp [zp]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf, he0norm, mul_one]
    linarith
  have hzm : ‖zm‖ ≤ r := by simpa only [zm, norm_neg] using hzp
  have hjoint (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) (hz : ‖z‖ ≤ r) :
      Integrable (fun p => Real.exp ⟪z, p⟫) ν := by
    have hm : Continuous (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => Real.exp ⟪z, p⟫) := by fun_prop
    refine hexp.mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((real_inner_le_norm z p).trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg p)))
  let i0 : Fin N := ⟨0, hN⟩
  have hp := (FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_408915f μ hf hβ hN zp (hjoint zp hzp)).2.1 i0
  have hn := (FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_408915f μ hf hβ hN zm (hjoint zm hzm)).2.1 i0
  have hzero : (WithLp.toLp 2 (fun _ : Fin n => (0 : ℝ)) : EuclideanSpace ℝ (Fin n)) = 0 := rfl
  have hplus : Integrable (fun x => Real.exp (t * f x)) μ := by
    simpa [zp, e0, hcoef, hzero] using hp
  have hminus : Integrable (fun x => Real.exp (-t * f x)) μ := by
    simpa [zm, zp, e0, neg_div, hcoef, hzero] using hn
  refine ⟨t, ht, ?_⟩
  refine (hplus.add hminus).mono'
    ((by fun_prop : Measurable (fun x => Real.exp (t * |f x|))).aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 (f x) with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le
