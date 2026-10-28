-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.memLp_id_two_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:14.544109+00:00
-- url     : https://prove2.me/submissions/f6d901bf-0c7c-4e1a-8677-5a923340e508

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Translation
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_readable

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Reconstruction is continuous. -/
theorem FunctionalInequalities.Probability.continuous_reconstruct (μ : ProbabilityMeasure E) : Continuous (reconstruct μ) :=
  (reconstruct μ).continuous
end Coordinates
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
/-- The intrinsic law of a log-concave probability has an exponential moment: some positive
rate `t` makes `exp (t ‖v‖)` integrable. This is the tail estimate behind the moment
conclusion and is stated separately because it is the form proved in the literature. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_exp_norm {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖))
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  ((borel_iff _).1 hμ.intrinsicMeasure).exists_integrable_exp_norm_readable
omit [CompleteSpace F] in
/-- The intrinsic law of a log-concave probability has finite moments of every order.
It follows from the exponential moment and Mathlib's `IntegrableExpMul`. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_norm_pow {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p)
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  obtain ⟨t, ht, hint⟩ := hμ.intrinsic_integrable_exp_norm
  exact Probability.integrable_norm_pow_of_integrable_exp_norm ht hint p
end
end Intrinsic
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : MeasureTheory.ProbabilityMeasure E} (hμ : FunctionalInequalities.KLS.LogConcave μ)
include hμ in
/-- The intrinsic law of a log-concave probability has a finite second moment, so its
covariance operator is the genuine centered covariance. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_memLp_id_two :
    MemLp id 2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  rw [memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id]
  simpa using hμ.intrinsic_integrable_norm_pow 2
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : MeasureTheory.ProbabilityMeasure E}
omit [CompleteSpace E] in
/-- A log-concave law has a finite ambient second moment: the intrinsic law has one and
reconstruction is an affine isometry. -/
theorem solution (hμ : FunctionalInequalities.KLS.LogConcave μ) : MemLp id 2 (μ : Measure E) := by
  have hν := hμ.intrinsic_memLp_id_two
  have h1 : MemLp (fun v ↦ FunctionalInequalities.Probability.reconstruct μ v) 2
      (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := by
    refine MemLp.of_le ((memLp_const ‖FunctionalInequalities.Probability.reconstruct μ 0‖).add hν.norm)
      (FunctionalInequalities.Probability.continuous_reconstruct μ).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    change ‖FunctionalInequalities.Probability.reconstruct μ v‖ ≤ ‖‖FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖v‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖FunctionalInequalities.Probability.reconstruct μ v‖ = ‖(FunctionalInequalities.Probability.reconstruct μ v - FunctionalInequalities.Probability.reconstruct μ 0) + FunctionalInequalities.Probability.reconstruct μ 0‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖FunctionalInequalities.Probability.reconstruct μ v - FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖FunctionalInequalities.Probability.reconstruct μ 0‖ := norm_add_le _ _
      _ = ‖v‖ + ‖FunctionalInequalities.Probability.reconstruct μ 0‖ := by
          rw [← dist_eq_norm, (FunctionalInequalities.Probability.reconstruct μ).dist_map, dist_zero_right]
      _ = ‖FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖v‖ := add_comm _ _
  have h2 : MemLp (fun x ↦ FunctionalInequalities.Probability.reconstruct μ (FunctionalInequalities.Probability.intrinsicMap μ x)) 2 (μ : Measure E) := by
    rw [← (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ).map_eq] at h1
    exact (memLp_map_measure_iff (FunctionalInequalities.Probability.continuous_reconstruct μ).aestronglyMeasurable
      (FunctionalInequalities.Probability.measurable_intrinsicMap μ).aemeasurable).mp h1
  exact h2.ae_eq (FunctionalInequalities.Probability.reconstruct_intrinsicMap_ae μ)
