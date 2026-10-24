-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:07:19.851007+00:00
-- url     : https://prove2.me/submissions/9573c10f-64cf-4015-bcbe-14203044680a

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_concave_tilt_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_map_affineIsometry_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- A measurable pushforward commutes with a pulled-back density. -/
theorem FunctionalInequalities.Probability.map_withDensity_comp
    (μ : Measure A) (f : A → B) (hf : Measurable f) (g : B → ENNReal) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    ← lintegral_indicator (hf hs), ← lintegral_indicator hs, lintegral_map (hg.indicator hs) hf]
  congr 1
/-- Pushforward of a tilt by a pulled-back exponent is the tilt of the pushforward. -/
theorem FunctionalInequalities.Probability.map_tilted_comp
    (μ : Measure A) (f : A → B) (hf : Measurable f) (φ : B → ℝ) (hφ : Measurable φ) :
    (μ.tilted (φ ∘ f)).map f = (μ.map f).tilted φ := by
  have hZ : (∫ y, Real.exp (φ y) ∂μ.map f) = ∫ x, Real.exp ((φ ∘ f) x) ∂μ := by
    simpa only [Function.comp_apply] using integral_map hf.aemeasurable hφ.exp.aestronglyMeasurable
  unfold Measure.tilted
  rw [hZ]
  simpa only [Function.comp_def] using Probability.map_withDensity_comp μ f hf
    (fun y => ENNReal.ofReal (Real.exp (φ y) / ∫ x, Real.exp ((φ ∘ f) x) ∂μ))
    (hφ.exp.div_const _).ennreal_ofReal
end MeasurableSpace
end TiltTransport
end
end
end

section
noncomputable section
open MeasureTheory Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq
omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure_408915f μ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty
end Intrinsic
end
end
end
end
end

section
noncomputable section
open MeasureTheory Set Topology Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
omit [CompleteSpace F] in
/-- Existence of a Borell density representative of the intrinsic law relative to any additive
Haar measure on the direction of the affine support. Absolute continuity is already proved; the
obligation is to choose an upper semicontinuous log-concave finite-valued version of the
Radon--Nikodym density. Includes dimension zero. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity {μ : ProbabilityMeasure F} (hμ : LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    ∃ ρ : (Probability.affineSupport μ).direction → ℝ,
      IsBorellDensity (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) m ρ :=
  hμ.intrinsicMeasure.exists_isBorellDensity_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty (hμ.intrinsic_absolutelyContinuous m)
end
end
end Intrinsic
end
end
end

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **A continuous concave tilt of a log-concave law is log-concave** (through the intrinsic Borell
representation; singular laws and dimension zero included). -/
theorem solution (μ ν : ProbabilityMeasure E) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) : FunctionalInequalities.KLS.LogConcave ν := by
  let F := (FunctionalInequalities.Probability.affineSupport μ).direction
  let ξ : ProbabilityMeasure F := FunctionalInequalities.Probability.intrinsicMeasure μ
  let e : F →ᵃⁱ[ℝ] E := FunctionalInequalities.Probability.reconstruct μ
  have he : (ξ : Measure F).map e = (μ : Measure E) :=
    (FunctionalInequalities.Probability.measurePreserving_reconstruct μ).map_eq
  have hi : Integrable (fun x => Real.exp (φ x)) (μ : Measure E) := by
    have h := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_408915f
      (ν := ν) (m := (μ : Measure E)) (W := -φ) (by simpa using hν)
    simpa using h
  have hi' : Integrable (fun x => Real.exp ((φ ∘ e) x)) (ξ : Measure F) :=
    (FunctionalInequalities.Probability.measurePreserving_reconstruct μ).integrable_comp
      (hφ.measurable.exp.aestronglyMeasurable) |>.mpr hi
  let η : ProbabilityMeasure F := ⟨(ξ : Measure F).tilted (φ ∘ e), isProbabilityMeasure_tilted hi'⟩
  obtain ⟨ρ, hρ⟩ := hLC.exists_isBorellDensity (volume : Measure F)
  have hconc' : ConcaveOn ℝ univ (φ ∘ e) := by
    simpa only [preimage_univ, AffineIsometry.coe_toAffineMap] using hconc.comp_affineMap e.toAffineMap
  have hη : FunctionalInequalities.KLS.LogConcave η :=
    (FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_408915f ξ η volume hρ (φ ∘ e) (hφ.comp e.continuous) hconc' rfl).compactLogConcave
  apply FunctionalInequalities.KLS.LogConcave.map_affineIsometry_408915f η hη ν e
  rw [hν]
  change (μ : Measure E).tilted φ = ((ξ : Measure F).tilted (φ ∘ e)).map e
  rw [FunctionalInequalities.Probability.map_tilted_comp _ e e.continuous.measurable φ hφ.measurable, he]
