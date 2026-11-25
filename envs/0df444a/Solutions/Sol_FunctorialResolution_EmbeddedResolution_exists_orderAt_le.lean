-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_orderAt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:30:34.908156+00:00
-- url     : https://prove2.me/submissions/3a4cf1bc-b319-4a7d-9a96-adbfd3e40a8d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_LocallyBoundedOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isOpen_setOf_stalkIdeal_eq_bot
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_algebraMap_sectionsAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClosed_orderAtLeastLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_subset_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_ne_top_of_stalkIdeal_ne_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem isLocallyNoetherian_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) :
    AlgebraicGeometry.IsLocallyNoetherian T.scheme := by
  have := hT.locallyOfFiniteType
  have : IsNoetherianRing T.base := inferInstance
  constructor
  intro U
  exact @isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U
    (sectionsAlgebra T.base T.structMap U.1)
    (algebraMap_sectionsAlgebra T.base T.structMap U.1)
private theorem stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) (x : ↥T.scheme) :
    stalkIdeal J x ≠ ⊥ := by
  have := isLocallyNoetherian_of_isAdmissible T hT
  intro hbot
  obtain ⟨y, hyC, hyJ⟩ := Set.not_subset.mp
    (hJ (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x))
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed ((J.support : Set ↥T.scheme)) := J.support.2
  obtain ⟨z, hzC, hz1, hz2⟩ :=
    hirr.2 {w : ↥T.scheme | stalkIdeal J w = ⊥} ((J.support : Set ↥T.scheme)ᶜ)
      (isOpen_setOf_stalkIdeal_eq_bot J) hcl.isOpen_compl
      ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩
  have hz1' : stalkIdeal J z = ⊥ := hz1
  have hztop : stalkIdeal J z = ⊤ := by
    by_contra hne
    exact hz2 ((mem_support_iff_stalkIdeal_ne_top J z).2 hne)
  have h1 : (1 : T.scheme.presheaf.stalk z) ∈ (⊥ : Ideal (T.scheme.presheaf.stalk z)) := by
    rw [← hz1', hztop]
    exact Submodule.mem_top
  rw [Ideal.mem_bot] at h1
  exact one_ne_zero h1
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) :
    ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt J x ≤ (B : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have := hT.locallyOfFiniteType
  have := isLocallyNoetherian_of_isAdmissible T hT
  have hfin : ∀ x : ↥T.scheme, orderAt J x ≠ ⊤ := fun x =>
    orderAt_ne_top_of_stalkIdeal_ne_bot J x
      (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents T hT J hJ x)
  have hclosed : ∀ m : ℕ, IsClosed (orderAtLeastLocus J m) := fun m =>
    isClosed_orderAtLeastLocus T.base T.structMap J m
  have hspec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of T.base))) := by
    simp
  have hcpt : IsCompact (Set.univ : Set ↥T.scheme) := by
    have h := hT.quasiCompact.isCompact_preimage Set.univ isOpen_univ hspec
    simpa using h
  have hempty : (Set.univ : Set ↥T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hx⟩
    have hx' := Set.mem_iInter.mp hx
    have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ orderAt J x := fun m => (mem_orderAtLeastLocus_iff J m x).1 (hx' m)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = (n : ℕ∞) :=
      ⟨(orderAt J x).toNat, (ENat.natCast_toNat (hfin x)).symm⟩
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      rw [← hn]
      exact h1 (n + 1)
    have h4 : n + 1 ≤ n := by exact_mod_cast h3
    omega
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed hempty
  have hMempty : ¬ ((Set.univ : Set ↥T.scheme) ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]
    exact hu
  refine ⟨u.sup id, fun x => ?_⟩
  have hxnot : x ∉ orderAtLeastLocus J (u.sup id) := by
    intro hx
    refine hMempty ⟨x, Set.mem_univ x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact orderAtLeastLocus_subset_of_le J (Finset.le_sup (f := id) hi) hx
  rw [mem_orderAtLeastLocus_iff] at hxnot
  exact le_of_lt (not_le.mp hxnot)
end FunctorialResolution.EmbeddedResolution
