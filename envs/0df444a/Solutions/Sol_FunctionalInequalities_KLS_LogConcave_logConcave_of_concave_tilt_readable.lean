-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:30:28.884742+00:00
-- url     : https://prove2.me/submissions/11943232-0eb2-48cc-8e51-a7201a91674c

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_ConcaveTilt
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_concave_tilt_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_map_affineIsometry_readable
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
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
  exact Probability.affineSupport_intrinsicMeasure_readable μ
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
section
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

section
noncomputable section
open MeasureTheory Set Topology Filter
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
section
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
end Intrinsic
end
end

noncomputable section
open MeasureTheory Set Filter Topology FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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
    have h := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable
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
    (FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_readable ξ η volume hρ (φ ∘ e) (hφ.comp e.continuous) hconc' rfl).compactLogConcave
  apply FunctionalInequalities.KLS.LogConcave.map_affineIsometry_readable η hη ν e
  rw [hν]
  change (μ : Measure E).tilted φ = ((ξ : Measure F).tilted (φ ∘ e)).map e
  rw [FunctionalInequalities.Probability.map_tilted_comp _ e e.continuous.measurable φ hφ.measurable, he]
