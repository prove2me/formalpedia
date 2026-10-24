-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_integral_bounded_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:24:51.145631+00:00
-- url     : https://prove2.me/submissions/cb9a2dd7-ae30-43e0-a9b8-e14853eda660

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
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
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_normalizedDensity_tendsto_L1_408915f

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedDensity ρ s) (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).mp
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
end
end
end
end
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Bornology
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section WeakConvergence
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_density_integrable {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) : Integrable ρ volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
    (ae_of_all _ fun y => hρ.nonneg y)).mp
  have h : μ Set.univ = 1 := measure_univ
  rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
  have hi : (∫⁻ y : E, ENNReal.ofReal (ρ y)) = 1 := by simpa only [Measure.restrict_univ] using h
  rw [hi]
  simp
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_integral (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (f : BoundedContinuousFunction E ℝ) : (∫ y, f y ∂(volume.withDensity (fun y => ENNReal.ofReal (g y)))) =
      ∫ y : E, g y * f y := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hg0 y), smul_eq_mul]
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bounded_density_integrable {g : E → ℝ} (hg : Integrable g volume)
    (f : BoundedContinuousFunction E ℝ) : Integrable (fun y => g y * f y) volume := by
  refine (hg.norm.mul_const ‖f‖).mono'
    (hg.aestronglyMeasurable.mul f.continuous.measurable.aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing in
/-- Integrals of bounded continuous functions against the smoothed laws converge to those against `μ`
(`L¹` convergence of the normalized densities). -/
theorem solution {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ) (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun s : ℝ => ∫ y, f y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) atTop (𝓝 (∫ y, f y ∂μ)) := by
  have hρi := source_density_integrable hρ
  have hlim : Tendsto (fun s : ℝ => ‖f‖ * ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y|)
      atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_408915f hρ).const_mul ‖f‖
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  have hFi := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity hρ hs
  have hFd := bounded_density_integrable hFi f
  have hρd := bounded_density_integrable hρi f
  have hdiff := hFi.sub hρi
  have hD := bounded_density_integrable hdiff f
  have hEq : (∫ y, f y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) - (∫ y, f y ∂μ) =
      ∫ y : E, (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y := by
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_withDensity_normalizedDensity hρ hs, ← hρ.withDensity_eq,
      density_integral _ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_measurable hρ.measurable hs)
        (fun y => (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_pos hρ hs y).le), density_integral _ hρ.measurable hρ.nonneg,
      ← integral_sub hFd hρd]
    congr 1
    funext y
    ring
  rw [hEq]
  calc
    ‖∫ y : E, (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ ≤
        ∫ y : E, ‖(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| * ‖f‖ := by
      apply integral_mono hD.norm (hdiff.abs.mul_const ‖f‖)
      intro y
      change ‖(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ ≤ |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| * ‖f‖
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (abs_nonneg _)
    _ = ‖f‖ * ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| := by rw [integral_mul_const]; ring
