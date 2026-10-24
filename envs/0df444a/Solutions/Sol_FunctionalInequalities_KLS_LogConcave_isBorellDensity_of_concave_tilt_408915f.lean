-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:06:11.907998+00:00
-- url     : https://prove2.me/submissions/5a7e58f4-d1ee-4c72-9e7d-d98112cb062c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
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
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_408915f

noncomputable section
open MeasureTheory Set Filter Topology FunctionalInequalities
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
private theorem FunctionalInequalities.KLS.LogConcave.upperSemicontinuous_mul_positive {E : Type*} [TopologicalSpace E] {f g : E → ℝ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) (hgpos : ∀ y, 0 < g y) :
    UpperSemicontinuous (fun y => f y * g y) := by
  intro y c hc
  obtain ⟨a, ha, hac⟩ := exists_between hc
  have hfu : f y < a / g y := (lt_div_iff₀ (hgpos y)).2 ha
  have htc : a / g y * g y < c := by
    simpa only [div_mul_cancel₀ a (hgpos y).ne'] using hac
  have hgc : ∀ᶠ z in 𝓝 y, a / g y * g z < c :=
    (hg.const_mul (a / g y)).continuousAt.eventually (isOpen_Iio.mem_nhds htc)
  filter_upwards [hf y _ hfu, hgc] with z hz hgz
  exact (mul_le_mul_of_nonneg_right hz.le (hgpos z).le).trans_lt hgz
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
omit [FiniteDimensional ℝ E] in
/-- A continuous concave tilt of a Borell density is a Borell density (zeros of the density allowed). -/
theorem solution (μ ν : ProbabilityMeasure E)
    (m : Measure E) {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity (μ : Measure E) m ρ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) :
    FunctionalInequalities.KLS.IsBorellDensity (ν : Measure E) m
      (fun x => ρ x * (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂(μ : Measure E))) := by
  have hi : Integrable (fun x => Real.exp (φ x)) (μ : Measure E) := by
    have h := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_408915f
      (ν := ν) (m := (μ : Measure E)) (W := -φ) (by simpa using hν)
    simpa using h
  let Z : ℝ := ∫ y, Real.exp (φ y) ∂(μ : Measure E)
  have hZ : 0 < Z := integral_exp_pos hi
  let g : E → ℝ := fun y => Real.exp (φ y) / Z
  have hg : Continuous g := (Real.continuous_exp.comp hφ).div_const _
  have hgp : ∀ y, 0 < g y := fun y => div_pos (Real.exp_pos _) hZ
  refine ⟨hρ.measurable.mul hg.measurable, fun x => mul_nonneg (hρ.nonneg x) (hgp x).le,
    upperSemicontinuous_mul_positive hρ.upperSemicontinuous hg hgp, ?_, ?_⟩
  · intro a b t ht0 ht1
    have hgLC : g a ^ t * g b ^ (1 - t) ≤ g (t • a + (1 - t) • b) := by
      simpa only [g, Pi.neg_apply, neg_neg] using
        FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_408915f hconc.neg hZ a b ht0 ht1
    have hρLC := hρ.logConcave a b t ht0 ht1
    change (ρ a * g a) ^ t * (ρ b * g b) ^ (1 - t) ≤ _
    rw [Real.mul_rpow (hρ.nonneg a) (hgp a).le, Real.mul_rpow (hρ.nonneg b) (hgp b).le]
    calc
      ρ a ^ t * g a ^ t * (ρ b ^ (1 - t) * g b ^ (1 - t)) =
          (ρ a ^ t * ρ b ^ (1 - t)) * (g a ^ t * g b ^ (1 - t)) := by ring
      _ ≤ _ := mul_le_mul hρLC hgLC
        (mul_nonneg (Real.rpow_nonneg (hgp a).le _) (Real.rpow_nonneg (hgp b).le _)) (hρ.nonneg _)
  · rw [hν]
    change m.withDensity (fun y => ENNReal.ofReal (ρ y * g y)) =
      (μ : Measure E).withDensity (fun y => ENNReal.ofReal (g y))
    have heq : (fun y => ENNReal.ofReal (ρ y * g y)) =
        (fun y => ENNReal.ofReal (ρ y)) * fun y => ENNReal.ofReal (g y) := by
      funext y
      exact ENNReal.ofReal_mul (hρ.nonneg y)
    rw [heq, withDensity_mul _ hρ.measurable.ennreal_ofReal hg.measurable.ennreal_ofReal,
      hρ.withDensity_eq]
