-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:23:23.085729+00:00
-- url     : https://prove2.me/submissions/cfc5bd5d-7c3b-4c5a-80e0-45bf6460c5af

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
import Theorems.Thm_FunctionalInequalities_KLS_IsBorellDensity_ae_continuous_408915f

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
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedDensity ρ s x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable]
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
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedKernel_scale (c : ℝ) (hc : 0 < c) (z : V) :
    normalizedKernel (c ^ 2) z =
      c ^ Module.finrank ℝ V * normalizedKernel 1 (c • z) := by
  unfold normalizedKernel kernel mass
  have hpow : (Real.pi / c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
      Real.pi ^ ((Module.finrank ℝ V : ℝ) / 2) / c ^ Module.finrank ℝ V := by
    rw [Real.div_rpow Real.pi_nonneg (sq_nonneg _)]
    have hd : (c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
        c ^ Module.finrank ℝ V := by
      calc
        (c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
            (c ^ (2 : ℝ)) ^ ((Module.finrank ℝ V : ℝ) / 2) := congrArg (fun x : ℝ => x ^ ((Module.finrank ℝ V : ℝ) / 2))
              (Real.rpow_natCast c 2).symm
        _ = c ^ ((2 : ℝ) * ((Module.finrank ℝ V : ℝ) / 2)) :=
          (Real.rpow_mul hc.le _ _).symm
        _ = c ^ (Module.finrank ℝ V : ℝ) := by congr 1; ring
        _ = c ^ Module.finrank ℝ V := Real.rpow_natCast c _
    rw [hd]
  rw [hpow]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  have he : -c ^ 2 * ‖z‖ ^ 2 = -(c * ‖z‖) ^ 2 := by ring
  rw [he]
  field_simp
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_integrable {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ) :
    Integrable ρ (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hρ.nonneg x)).mp
  have hmass : (∫⁻ x : V, ENNReal.ofReal (ρ x)) = 1 := by
    have h : ν univ = 1 := measure_univ
    rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
    simpa only [Measure.restrict_univ] using h
  rw [hmass]
  simp
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tendsto_norm_pow_normalizedKernel_one :
    Tendsto (fun z : V => ‖z‖ ^ Module.finrank ℝ V * normalizedKernel 1 z)
      (cobounded V) (𝓝 0) := by
  have A : Tendsto (fun z : V => ‖z‖ ^ 2) (cobounded V) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have B := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((Module.finrank ℝ V : ℝ) / 2) 1 zero_lt_one).comp A
  have C := B.const_mul (mass (V := V) 1)⁻¹
  rw [mul_zero] at C
  convert C using 2 with z
  simp only [normalizedKernel, kernel, mass, div_one, Function.comp_apply]
  have hnorm : (‖z‖ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
      ‖z‖ ^ Module.finrank ℝ V := by
    calc
      (‖z‖ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
          (‖z‖ ^ (2 : ℝ)) ^ ((Module.finrank ℝ V : ℝ) / 2) :=
            congrArg (fun x : ℝ => x ^ ((Module.finrank ℝ V : ℝ) / 2))
              (Real.rpow_natCast ‖z‖ 2).symm
      _ = ‖z‖ ^ ((2 : ℝ) * ((Module.finrank ℝ V : ℝ) / 2)) :=
        (Real.rpow_mul (norm_nonneg z) _ _).symm
      _ = ‖z‖ ^ (Module.finrank ℝ V : ℝ) := by congr 1; ring
      _ = ‖z‖ ^ Module.finrank ℝ V := Real.rpow_natCast ‖z‖ _
  rw [hnorm]
  ring
/-- At each continuity point of the source Borell density, Gaussian smoothing
recovers that density as its inverse length scale tends to infinity. -/
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_at_continuity_sq {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {x : V} (hx : ContinuousAt ρ x) :
    Tendsto (fun c : ℝ => normalizedDensity ρ (c ^ 2) x) atTop (𝓝 (ρ x)) := by
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := (volume : Measure V)) (φ := normalizedKernel (V := V) 1)
    (fun z => (normalizedKernel_pos one_pos z).le)
    (integral_normalizedKernel (V := V) one_pos)
    (tendsto_norm_pow_normalizedKernel_one (V := V))
    (source_integrable hρ) hx
  apply hpeak.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  rw [normalizedDensity_eq_integral hρ (sq_pos_of_pos hc) x]
  rw [← hρ.withDensity_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hρ.nonneg y), normalizedKernel_scale c hc (x - y)]
  simp only [smul_eq_mul]
  ring
/-- The normalized Gaussian smoothing density tends to the source Borell
density at every continuity point as the inverse variance tends to infinity. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_at_continuity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {x : V} (hx : ContinuousAt ρ x) :
    Tendsto (fun s : ℝ => normalizedDensity ρ s x) atTop (𝓝 (ρ x)) := by
  have h := (normalizedDensity_tendsto_at_continuity_sq hρ hx).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs
  change normalizedDensity ρ ((√s) ^ 2) x = normalizedDensity ρ s x
  rw [Real.sq_sqrt hs]
/-- The actual normalized Gaussian density converges to the source Borell
density Haar-almost everywhere. This statement does not yet give convergence
of the associated probability measures. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_ae_tendsto {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    ∀ᵐ x ∂(volume : Measure V),
      Tendsto (fun s : ℝ => normalizedDensity ρ s x) atTop (𝓝 (ρ x)) :=
  (hρ.ae_continuous_408915f).mono fun _ hx => normalizedDensity_tendsto_at_continuity hρ hx
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tendsto_integral_min {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    Tendsto (fun s : ℝ => ∫ x : V, min (normalizedDensity ρ s x) (ρ x))
      atTop (𝓝 (∫ x : V, ρ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := ρ)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact ((normalizedDensity_measurable hρ.measurable hs).min hρ.measurable).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact Filter.Eventually.of_forall fun x => by
      have h0 : 0 ≤ min (normalizedDensity ρ s x) (ρ x) :=
        le_min (normalizedDensity_pos hρ hs x).le (hρ.nonneg x)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _
  · apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hρ.nonneg x)).mp
    have hmass : (∫⁻ x : V, ENNReal.ofReal (ρ x)) = 1 := by
      have h : ν univ = 1 := measure_univ
      rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
      simpa only [Measure.restrict_univ] using h
    rw [hmass]
    simp
  · filter_upwards [normalizedDensity_ae_tendsto hρ] with x hx
    simpa only [min_self] using hx.min (tendsto_const_nhds (x := ρ x))
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_integral_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    ∫ x : V, ρ x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => hρ.nonneg x)
    hρ.measurable.aestronglyMeasurable]
  have h : ν univ = 1 := measure_univ
  rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
  simpa only [Measure.restrict_univ, ENNReal.toReal_one] using congrArg ENNReal.toReal h
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_min {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : V => min (normalizedDensity ρ s x) (ρ x)) volume := by
  apply (source_integrable hρ).mono'
  · exact ((normalizedDensity_measurable hρ.measurable hs).min hρ.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (normalizedDensity_pos hρ hs x).le (hρ.nonneg x))]
      exact min_le_right _ _
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing in
/-- Normalized Gaussian smoothing converges to the source Borell density
in `L¹(volume)` as inverse variance tends to infinity. The proof uses
unit mass and dominated convergence for the pointwise minimum. -/
theorem solution {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ) :
    Tendsto (fun s : ℝ => ∫ x : V, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x - ρ x|)
      atTop (𝓝 0) := by
  have heq (s : ℝ) (hs : 0 < s) :
      (∫ x : V, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x - ρ x|) =
        (∫ x : V, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) + (∫ x : V, ρ x) -
          2 * (∫ x : V, min (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x)) := by
    have hp (x : V) : |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x - ρ x| =
        FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x + ρ x - 2 * min (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x) := by
      rcases le_total (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hp]
    calc
      (∫ x : V, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x + ρ x -
          2 * min (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x)) =
          (∫ x : V, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x + ρ x) -
            (∫ x : V, 2 * min (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x)) :=
        integral_sub ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity hρ hs).add (source_integrable hρ))
          ((integrable_min hρ hs).const_mul 2)
      _ = _ := by rw [integral_add (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity hρ hs)
        (source_integrable hρ), integral_const_mul]
  have hlim : Tendsto (fun s : ℝ =>
      (2 : ℝ) - 2 * (∫ x : V, min (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x) (ρ x)))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
      ((tendsto_integral_min hρ).const_mul 2)
    simpa [source_integral_eq_one hρ] using h
  apply hlim.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  rw [heq s hs, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedDensity_eq_one hρ hs, source_integral_eq_one hρ]
  norm_num
