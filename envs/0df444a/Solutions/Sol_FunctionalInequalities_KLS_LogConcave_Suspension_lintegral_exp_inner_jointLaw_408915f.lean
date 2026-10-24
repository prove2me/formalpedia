-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:02:40.244026+00:00
-- url     : https://prove2.me/submissions/0d3529ea-06a7-4c34-a6f1-9c438806e93b

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
import Theorems.Thm_FunctionalInequalities_Probability_lintegral_pi_prod_fin_408915f

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
/-- **Factorization of the joint Laplace transform** (BKL p. 28), in extended nonnegative form:
`∫⁻ e^{⟪z, p⟫} dν = (∫⁻ e^{(z₀/σ) s} dη_β) · Π_i ∫⁻ e^{(z₀/(σ√N)) f + ⟪z_i, x⟫} dμ`. -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [SigmaFinite μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (β σ : ℝ)
    [SigmaFinite (FunctionalInequalities.Probability.Line.laplaceMeasure β)] (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :
    ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂(FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N) =
      (∫⁻ s, ENNReal.ofReal (Real.exp (z none / σ * s)) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
        ∏ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) ∂μ := by
    classical
    have hinner :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ⟪z, FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N (x, s)⟫ =
            z none / σ * s +
              ∑ i : Fin N,
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫) := by
      intro x s
      simp only [FunctionalInequalities.KLS.LogConcave.Suspension.embed, FunctionalInequalities.KLS.LogConcave.Suspension.copyStat, PiLp.inner_apply, Fintype.sum_option,
        Fintype.sum_prod_type, Option.elim_none, Option.elim_some,
        Real.inner_apply, div_eq_mul_inv, mul_inv_rev]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

    have hintegrand :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ENNReal.ofReal (Real.exp ⟪z, FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N (x, s)⟫) =
            ENNReal.ofReal (Real.exp (z none / σ * s)) *
              ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
      intro x s
      rw [hinner, Real.exp_add, Real.exp_sum,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hfin :
          ENNReal.ofReal
              (∏ i : Fin N, Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) =
            ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
        simpa using
          (ENNReal.ofReal_prod_of_nonneg
            (s := (Finset.univ : Finset (Fin N)))
            (fun i _ => (Real.exp_pos
              (z none / (σ * Real.sqrt N) * f (x i) +
                ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                    EuclideanSpace ℝ (Fin n)), x i⟫)).le))
      rw [hfin]

    have hmeas :
        Measurable (FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N) := by
      have hg :
          Measurable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim ((FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
        rw [measurable_pi_iff]
        intro o
        cases o with
        | none =>
            unfold FunctionalInequalities.KLS.LogConcave.Suspension.copyStat
            measurability
        | some ij =>
            measurability
      unfold FunctionalInequalities.KLS.LogConcave.Suspension.embed
      exact (WithLp.measurable_toLp 2 _).comp hg

    rw [FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw, lintegral_map (by fun_prop) hmeas]
    simp_rw [hintegrand]

    let gi : Fin N → EuclideanSpace ℝ (Fin n) → ENNReal := fun i x =>
      ENNReal.ofReal (Real.exp
        (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
              EuclideanSpace ℝ (Fin n)), x⟫))
    let G : (Fin N → EuclideanSpace ℝ (Fin n)) → ENNReal := fun x =>
      ∏ i : Fin N, gi i (x i)
    let H : ℝ → ENNReal := fun s =>
      ENNReal.ofReal (Real.exp (z none / σ * s))

    have hG : Measurable G := by
      dsimp [G, gi]
      measurability
    have hH : Measurable H := by
      dsimp [H]
      fun_prop

    have hpi :
        (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) =
          ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      simpa [G] using
        (FunctionalInequalities.Probability.lintegral_pi_prod_fin_408915f μ N gi (by
          intro i
          dsimp [gi]
          measurability))

    have hmain :
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) =
          (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      calc
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β))) =
            ∫⁻ a, G a.1 * H a.2
              ∂((Measure.pi fun _ : Fin N => μ).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β)) :=
          lintegral_congr fun a => mul_comm _ _
        _ = (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) *
            (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
          lintegral_prod_mul hG.aemeasurable hH.aemeasurable
        _ = (∫⁻ s, H s ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
          rw [hpi, mul_comm]

    simpa [G, H, gi] using hmain
