-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:04:23.109901+00:00
-- url     : https://prove2.me/submissions/8c3b4a1d-8a12-49be-baa6-4003a8b232bf

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_lintegral_exp_inner_jointLaw_408915f

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
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_pos_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Measurable g) :
    0 < ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂μ := by
  have hs : Function.support (fun x => ENNReal.ofReal (Real.exp (g x))) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos (g x))).ne'
  rw [lintegral_pos_iff_support (hg.exp.ennreal_ofReal), hs, measure_univ]
  norm_num
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.fin_prod_factor_ne_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ENNReal) (hb : ∀ i, b i ≠ 0) (hprod : (∏ i, b i) ≠ ⊤) (i : ι) :
    b i ≠ ⊤ := by
  have hrest : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hmul : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) * b i ≠ ⊤ := by
    rw [Finset.prod_erase_mul _ _ (by simp)]
    exact hprod
  exact (ENNReal.lt_top_of_mul_ne_top_right hmul hrest).ne
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- Joint integrability forces every strictly positive Laplace product factor to be finite. -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (_hN : 0 < N) (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    Integrable (fun s : ℝ => Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) ∧
      (∀ i : Fin N, Integrable (fun x => Real.exp
        (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) μ) ∧
      (∫ p, Real.exp ⟪z, p⟫ ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) =
        (∫ s : ℝ, Real.exp (z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β) *
          ∏ i : Fin N, ∫ x, Real.exp
            (z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
              ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ := by
  classical
  let _ : IsProbabilityMeasure (FunctionalInequalities.Probability.Line.laplaceMeasure β) := FunctionalInequalities.Probability.Line.isProbabilityMeasure_laplaceMeasure hβ
  let noise : ℝ → ℝ := fun s => z none / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s
  let copy : Fin N → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    z none / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
      ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫
  let A : ENNReal := ∫⁻ s, ENNReal.ofReal (Real.exp (noise s)) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β
  let B : Fin N → ENNReal := fun i => ∫⁻ x, ENNReal.ofReal (Real.exp (copy i x)) ∂μ
  let J : ENNReal := ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  have hmNoise : Measurable noise := by dsimp [noise]; fun_prop
  have hmCopy (i : Fin N) : Measurable (copy i) := by dsimp [copy]; measurability
  have hApos : 0 < A := lintegral_exp_pos_probability (FunctionalInequalities.Probability.Line.laplaceMeasure β) noise hmNoise
  have hBpos (i : Fin N) : 0 < B i := lintegral_exp_pos_probability μ (copy i) (hmCopy i)
  have hJfinite : J ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr hInt
  have hfactor : J = A * ∏ i, B i := by
    exact FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw_408915f μ hf β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) z
  have htotal : A * ∏ i, B i ≠ ⊤ := hfactor.symm ▸ hJfinite
  have hprodNonzero : (∏ i, B i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hBpos i).ne')
  have hAfinite : A ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_left htotal hprodNonzero).ne
  have hprodFinite : (∏ i, B i) ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right htotal hApos.ne').ne
  have hBfinite (i : Fin N) : B i ≠ ⊤ :=
    fin_prod_factor_ne_top B (fun i => (hBpos i).ne') hprodFinite i
  have hNoise : Integrable (fun s => Real.exp (noise s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) :=
    (lintegral_ofReal_ne_top_iff_integrable hmNoise.exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp hAfinite
  have hCopy (i : Fin N) : Integrable (fun x => Real.exp (copy i x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hmCopy i).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp (hBfinite i)
  have hJreal : J.toReal = ∫ p, Real.exp ⟪z, p⟫ ∂FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hInt.aestronglyMeasurable).symm
  have hAreal : A.toReal = ∫ s, Real.exp (noise s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hNoise.aestronglyMeasurable).symm
  have hBreal (i : Fin N) : (B i).toReal = ∫ x, Real.exp (copy i x) ∂μ :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) (hCopy i).aestronglyMeasurable).symm
  have hreal := congrArg ENNReal.toReal hfactor
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, hJreal, hAreal] at hreal
  simp_rw [hBreal] at hreal
  exact ⟨hNoise, hCopy, hreal⟩
