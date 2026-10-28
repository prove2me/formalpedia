-- Prove2me | solution 1 for FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:34.916147+00:00
-- url     : https://prove2.me/submissions/5a2dea96-fa39-4055-a838-6dbeb1343854

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_readable

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
/-- The affine support is the smallest closed affine subspace of full measure. -/
theorem FunctionalInequalities.Probability.affineSupport_le_of_ae_mem (μ : ProbabilityMeasure E) (A : AffineSubspace ℝ E)
    (hA : IsClosed (A : Set E)) (hμ : ∀ᵐ x ∂(μ : Measure E), x ∈ A) :
    affineSupport μ ≤ A := by
  apply affineSpan_le.mpr
  exact Measure.support_subset_of_isClosed hA hμ
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On the affine support, the retraction is the identity. -/
@[simp]
theorem FunctionalInequalities.Probability.coe_retraction_of_mem (μ : ProbabilityMeasure E) {x : E}
    (hx : x ∈ affineSupport μ) : (retraction μ x : E) = x := by
  classical
  simp [retraction, hx]
end Coordinates
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
omit [CompleteSpace E] [BorelSpace E] in
/-- Intrinsic coordinates are, almost everywhere, the orthogonal projection of the displacement
from the chosen support point onto the direction space. -/
theorem FunctionalInequalities.Probability.intrinsicMap_ae_eq_orthogonalProjection (μ : ProbabilityMeasure E) :
    intrinsicMap μ =ᵐ[(μ : Measure E)]
      fun x ↦ (affineSupport μ).direction.orthogonalProjectionOnto (x - supportPoint μ) := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  have hdir : x - supportPoint μ ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hx (origin μ).property
  have hret : retraction μ x = ⟨x, hx⟩ := Subtype.ext (coe_retraction_of_mem μ hx)
  rw [intrinsicMap, hret, coordinateEquiv, AffineIsometryEquiv.coe_vaddConst_symm]
  apply Subtype.ext
  rw [← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hdir]
  rfl
omit [CompleteSpace E] in
/-- The intrinsic law keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_intrinsicMeasure (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) :
    MemLp id 2 (intrinsicMeasure μ : Measure (affineSupport μ).direction) := by
  set P := (affineSupport μ).direction.orthogonalProjectionOnto
  have h1 : MemLp (fun x ↦ x - supportPoint μ) 2 (μ : Measure E) := hμ.sub (memLp_const _)
  have h2 : MemLp (fun x ↦ P (x - supportPoint μ)) 2 (μ : Measure E) := P.comp_memLp' h1
  have h3 : MemLp (intrinsicMap μ) 2 (μ : Measure E) :=
    h2.ae_eq (intrinsicMap_ae_eq_orthogonalProjection μ).symm
  rw [intrinsicMeasure, ProbabilityMeasure.toMeasure_map]
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_intrinsicMap μ).aemeasurable).2 h3
end
open FunctionalInequalities.Probability
omit [CompleteSpace E] in
/-- The intrinsic covariance operator is positive definite on the direction space. -/
theorem solution (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {v : (FunctionalInequalities.Probability.affineSupport μ).direction} (hv : v ≠ 0) :
    0 < inner ℝ (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) v) v := by
  set ν := FunctionalInequalities.Probability.intrinsicMeasure μ
  have hν : MemLp id 2 (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := FunctionalInequalities.Probability.memLp_id_two_intrinsicMeasure μ hμ
  rw [FunctionalInequalities.Covariance.operator_inner, covarianceBilin_self hν]
  rcases (variance_nonneg (fun u ↦ inner ℝ v u) (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction)).lt_or_eq with h | h
  · exact h
  exfalso
  have hX : MemLp (fun u ↦ inner ℝ v u) 2 (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := by
    have := (innerSL ℝ v).comp_memLp' hν
    simpa [Function.comp] using this
  have hev : evariance (fun u ↦ inner ℝ v u) (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) = 0 := by
    rw [← ofReal_variance hX, ← h, ENNReal.ofReal_zero]
  have hae := (evariance_eq_zero_iff hX.aestronglyMeasurable.aemeasurable).mp hev
  set c : ℝ := ∫ u, inner ℝ v u ∂(ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction)
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set H : AffineSubspace ℝ (FunctionalInequalities.Probability.affineSupport μ).direction := AffineSubspace.mk' ((c / ‖v‖ ^ 2) • v) (Submodule.span ℝ {v})ᗮ
  have hHclosed : IsClosed (H : Set (FunctionalInequalities.Probability.affineSupport μ).direction) := H.closed_of_finiteDimensional
  have hmem : ∀ᵐ u ∂(ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction), u ∈ H := by
    filter_upwards [hae] with u hu
    have hu' : inner ℝ v u = c := hu
    rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu',
      div_mul_cancel₀ c (pow_ne_zero 2 hv'), sub_self]
  have hle := FunctionalInequalities.Probability.affineSupport_le_of_ae_mem ν H hHclosed hmem
  rw [FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_readable] at hle
  have hH : H = ⊤ := top_le_iff.mp hle
  have hdir : (Submodule.span ℝ {v})ᗮ = ⊤ := by
    have := congrArg AffineSubspace.direction hH
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at this
  exact hv (Submodule.span_singleton_eq_bot.mp ((Submodule.orthogonal_eq_top_iff _).mp hdir))
