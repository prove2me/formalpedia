-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:01:15.905527+00:00
-- url     : https://prove2.me/submissions/a0ca3271-98d3-4494-bb42-b53c152cd194

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_scalar_moments_408915f
import Theorems.Thm_FunctionalInequalities_Probability_integral_normalizedSum_mul_comp_eval_pi_408915f
import Theorems.Thm_FunctionalInequalities_Probability_integral_prod_add_mul_eq_zero_408915f
import Theorems.Thm_FunctionalInequalities_Probability_pi_normalizedSum_moments_408915f

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
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
/-- The copy statistic `F_N = (Σ_i f(X_i))/√N` has mean `0` and second moment `1`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) :
    MemLp (copyStat f N) 2 (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x, copyStat f N x ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x, (copyStat f N x) ^ 2 ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by
  exact pi_normalizedSum_moments_408915f μ f hf2 hf0 hf1 N hN
/-- Linear functionals of a law with finite second moment are in `L²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.memLp_inner {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => ⟪u, x⟫) 2 μ := by
  simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
/-- Linear functionals of a centered law are centered. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_inner_eq_zero {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (u : EuclideanSpace ℝ (Fin n)) : (∫ x, ⟪u, x⟫ ∂μ) = 0 := by
  calc
    _ = ⟪u, ∫ x, x ∂μ⟫ :=
      (innerSL ℝ u).integral_comp_comm (hμ2.integrable one_le_two)
    _ = 0 := by rw [hμ0]; simp
/-- `E[F_N ⟪u, X_i⟫] = 0` when `f` is orthogonal to the linear functions. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_copyStat_mul_inner {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin n) => copyStat f N x * ⟪u, x i⟫)
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ (Fin n), copyStat f N x * ⟪u, x i⟫
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by
  have hfg : (∫ x, f x * ⟪u, x⟫ ∂μ) = 0 := by
    calc
      _ = ∫ x, ⟪u, x⟫ * f x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
      _ = 0 := hfx u
  exact integral_normalizedSum_mul_comp_eval_pi_408915f μ f (fun x => ⟪u, x⟫) hf2
    (memLp_inner μ hμ2 u) hf0 (integral_inner_eq_zero μ hμ2 hμ0 u) hfg N hN i
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- `E[S ⟪u, X_i⟫] = 0`. -/
theorem solution {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (FunctionalInequalities.Probability.Line.laplaceMeasure β))
    (hη0 : ∫ s, s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂FunctionalInequalities.Probability.Line.laplaceMeasure β = 2 / β ^ 2)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫)
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) = 0 := by
  have hF := FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments hN μ f hf2 hf0 hf1
  have hS := FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_408915f hN μ f hf2 hf0 hf1 hβ hη1 hη2 hη0 hηv
  have hZμ2 : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
  have hZ2 : MemLp (fun x : Fin N → EuclideanSpace ℝ (Fin n) => ⟪u, x i⟫) 2
      (Measure.pi (fun _ : Fin N => μ)) :=
    hZμ2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hZprod2 := hZ2.comp_fst (FunctionalInequalities.Probability.Line.laplaceMeasure β)
  have hprod : MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫) 1
      ((Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) :=
    hZprod2.mul' hS.1
  have hηL2 : MemLp (fun s : ℝ => s) 2 (FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
    (memLp_two_iff_integrable_sq_norm hη1.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hη2)
  have hCX := FunctionalInequalities.KLS.LogConcave.Suspension.integral_copyStat_mul_inner hN μ hμ2 hμ0 f hf2 hf0 hfx i u
  have hbase := FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_408915f (Measure.pi (fun _ : Fin N => μ)) (FunctionalInequalities.Probability.Line.laplaceMeasure β)
    (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N) (fun x => ⟪u, x i⟫) (fun s : ℝ => s) hF.1 hZ2 hηL2 hCX.2 hη0
  refine ⟨hprod.integrable le_rfl, ?_⟩
  have heq : (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) * ⟪u, q.1 i⟫) =
      (fun q => ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) * ⟪u, q.1 i⟫) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) := by
    funext q
    ring
  rw [heq, integral_div, hbase.2]
  simp
