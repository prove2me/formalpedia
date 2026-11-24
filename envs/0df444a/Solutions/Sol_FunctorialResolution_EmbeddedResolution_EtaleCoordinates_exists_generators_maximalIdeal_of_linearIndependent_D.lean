-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_generators_maximalIdeal_of_linearIndependent_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:22.864132+00:00
-- url     : https://prove2.me/submissions/dc7b8f3b-0495-48ad-a993-7f7f7836a6ed

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_span_range_eq_span_range_of_eq_mul_isUnit
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_KaehlerDifferential_residue_tmul_D_mul_of_mem_maximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange



set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (k : Type*) [CommRing k] (S : Type*) [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (h : ℕ) (y : Fin h → A)
    (hspan : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A)
    (hindep : LinearIndependent (IsLocalRing.ResidueField A)
      fun i : Fin h =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) :
    ∃ s : Fin h → S,
      (∀ i : Fin h, s i ∈ q) ∧
      Ideal.span (Set.range fun i : Fin h => algebraMap S A (s i)) =
        IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (algebraMap S A (s i)) := by
  classical
  choose p hp using fun i : Fin h =>
    IsLocalization.surj (M := q.primeCompl) (S := A) (y i)
  obtain ⟨s, c, hcu, hmul⟩ : ∃ (s : Fin h → S) (c : Fin h → A),
      (∀ i, IsUnit (c i)) ∧ ∀ i, algebraMap S A (s i) = y i * c i :=
    ⟨fun i => (p i).1, fun i => algebraMap S A ((p i).2 : S),
      fun i => IsLocalization.map_units (M := q.primeCompl) (S := A) ((p i).2),
      fun i => (hp i).symm⟩
  have hymem : ∀ i : Fin h, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i
    by_contra hni
    have hunit : IsUnit (algebraMap S A (s i)) :=
      IsLocalization.map_units (M := q.primeCompl) (S := A) ⟨s i, hni⟩
    have hmem : algebraMap S A (s i) ∈ IsLocalRing.maximalIdeal A := by
      rw [hmul i]
      exact Ideal.mul_mem_right _ _ (hymem i)
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
  · refine Eq.trans ?_ hspan
    exact span_range_eq_span_range_of_eq_mul_isUnit y
      (fun i : Fin h => algebraMap S A (s i)) c hcu hmul
  · have hne : ∀ i : Fin h, IsLocalRing.residue A (c i) ≠ 0 := fun i =>
      ((hcu i).map (IsLocalRing.residue A)).ne_zero
    have hfun : (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      rw [hmul i]
      exact KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c i) (hymem i)
    have hsmul : ((fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i)) •
        fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      simp [Units.smul_def]
    have key := hindep.units_smul
      (fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i))
    rw [hfun, ← hsmul]
    exact key
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
