-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.sum_sq_cumulant_ge_of_entries_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:02:15.466374+00:00
-- url     : https://prove2.me/submissions/001cd28f-4c45-463e-8e28-3fb456a3b75f

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
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_sq_blocks_le_408915f

section
noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
section FiniteIndex
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
/-- If every block entry is `c` times a common array `T`, the block energy `|κ| c² |T|²` is at most
the whole Hilbert–Schmidt energy (the source's use, with `|κ| = N` and `c = d!/(σ√N)`). -/
theorem FunctionalInequalities.Analysis.Tensor.card_mul_sq_mul_sum_sq_le_of_blocks {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) (c : ℝ)
    (T : (Fin d → ι) → ℝ) (hA : ∀ i j, A (fun k => some (i, j k)) = c * T j) :
    (Fintype.card κ : ℝ) * c ^ 2 * ∑ j, T j ^ 2 ≤ ∑ J, A J ^ 2 := by
  have h := sum_sq_blocks_le_408915f hd A
  simp only [hA, mul_pow, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith
end FiniteIndex
end
end
end
end
end

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end
end
end

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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Hilbert–Schmidt lower bound from (112)** (BKL p. 29). -/
theorem solution {n N : ℕ} (hN : 0 < N) (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    {d : ℕ} (hd : 1 ≤ d)
    (h112 : ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
      FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
        if ∀ k k', I k = I k' then
          (d.factorial : ℝ) / (σ * Real.sqrt N) *
            FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
        else 0) :
    (d.factorial : ℝ) ^ 2 / σ ^ 2 *
        ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ^ 2 ≤
      ∑ K : Fin d → Option (Fin N × Fin n),
        FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (K k) 1) ^ 2 := by
  classical
  have h := FunctionalInequalities.Analysis.Tensor.card_mul_sq_mul_sum_sq_le_of_blocks (κ := Fin N) (ι := Fin n) (by omega)
    (fun K => FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
      EuclideanSpace.single (K k) 1))
    ((d.factorial : ℝ) / (σ * Real.sqrt N))
    (fun J => FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
    (fun i j => by simpa using h112 (fun _ => i) j)
  have hnorm : ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ^ 2 =
      ∑ J : Fin d → Fin n,
        (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
  have hsqrt : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hc : (Fintype.card (Fin N) : ℝ) * ((d.factorial : ℝ) / (σ * Real.sqrt N)) ^ 2 =
      (d.factorial : ℝ) ^ 2 / σ ^ 2 := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Fintype.card_fin, div_pow, mul_pow, hsqrt]
    field_simp
  rw [hc] at h
  rw [hnorm]
  exact h
