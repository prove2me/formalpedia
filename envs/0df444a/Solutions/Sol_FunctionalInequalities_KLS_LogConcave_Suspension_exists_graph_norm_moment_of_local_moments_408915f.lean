-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:02:41.558789+00:00
-- url     : https://prove2.me/submissions/847cccbd-a67c-4c89-b70b-30cf03aeeb5b

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
/-- **Exponential moment of the graph law** `x ↦ (f x, x)` from exponential moments of `|f|` and
`‖x‖` (Cauchy–Schwarz in `L²`, at rate `min a s / 2`). -/
theorem solution {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hfa : Integrable (fun x => Real.exp (a * |f x|)) μ)
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Option (Fin n)) :=
    fun x => WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
  have hgm : Measurable g := by
    dsimp [g]
    apply (WithLp.measurable_toLp 2 _).comp
    rw [measurable_pi_iff]
    intro o
    cases o with
    | none => exact hf
    | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have hsq (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
    change (f x) ^ 2 + ∑ j : Fin n, (x j) ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2
    rw [sq_abs, ← EuclideanSpace.real_norm_sq_eq]
  have hbound (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ≤ |f x| + ‖x‖ := by
    nlinarith [hsq x, norm_nonneg (g x), abs_nonneg (f x), norm_nonneg x,
      mul_nonneg (abs_nonneg (f x)) (norm_nonneg x)]
  let t : ℝ := min a s / 2
  have ht : 0 < t := div_pos (lt_min ha hs) (by norm_num)
  have h2a : 2 * t ≤ a := by dsimp [t]; linarith [min_le_left a s]
  have h2s : 2 * t ≤ s := by dsimp [t]; linarith [min_le_right a s]
  let U : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * |f x|)
  let V : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * ‖x‖)
  have hmU : AEStronglyMeasurable U μ :=
    (by fun_prop : Measurable U).aestronglyMeasurable
  have hmV : AEStronglyMeasurable V μ :=
    (by fun_prop : Continuous V).aestronglyMeasurable
  have hU2 : Integrable (fun x => U x ^ 2) μ := by
    refine hfa.mono' ((by fun_prop : Measurable (fun x => U x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [U]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * |f x| + t * |f x| = (2 * t) * |f x| := by ring
      _ ≤ a * |f x| := mul_le_mul_of_nonneg_right h2a (abs_nonneg _)
  have hV2 : Integrable (fun x => V x ^ 2) μ := by
    refine hxs.mono' ((by fun_prop : Continuous (fun x => V x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [V]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * ‖x‖ + t * ‖x‖ = (2 * t) * ‖x‖ := by ring
      _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right h2s (norm_nonneg _)
  have hULp : MemLp U 2 μ := (memLp_two_iff_integrable_sq hmU).mpr hU2
  have hVLp : MemLp V 2 μ := (memLp_two_iff_integrable_sq hmV).mpr hV2
  have hUV : Integrable (fun x => U x * V x) μ := hULp.integrable_mul hVLp
  have hgint : Integrable (fun x => Real.exp (t * ‖g x‖)) μ := by
    refine hUV.mono'
      ((by fun_prop : Measurable (fun x => Real.exp (t * ‖g x‖))).aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [U, V]
    calc
      Real.exp (t * ‖g x‖) ≤ Real.exp (t * (|f x| + ‖x‖)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound x) ht.le)
      _ = Real.exp (t * |f x|) * Real.exp (t * ‖x‖) := by rw [mul_add, Real.exp_add]
  refine ⟨t, ht, ?_⟩
  exact (integrable_map_measure
    ((by fun_prop : Continuous
      (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))).aestronglyMeasurable)
    hgm.aemeasurable).mpr hgint
