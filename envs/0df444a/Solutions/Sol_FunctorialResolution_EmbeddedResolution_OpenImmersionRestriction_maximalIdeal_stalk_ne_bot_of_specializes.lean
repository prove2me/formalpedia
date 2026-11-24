-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.maximalIdeal_stalk_ne_bot_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:40.722147+00:00
-- url     : https://prove2.me/submissions/9e26b833-a81d-4641-934e-23f6945ff4fb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealOrderOne
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
private theorem exists_affineOpens_mem (X : Scheme.{u}) (x : ↥X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution
    (X : Scheme.{u}) (x y : ↥X) (h : y ⤳ x) (hne : y ≠ x) :
    IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ := by
  intro hbot
  obtain ⟨U, hxU0⟩ := exists_affineOpens_mem X x
  have hxU : x ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hmem : x ∈ closure ({y} : Set ↥X) := specializes_iff_mem_closure.mp h
  have hyU : y ∈ U.1 := by
    have hopen : IsOpen ((U.1 : Set ↥X)) := U.1.2
    obtain ⟨z, hzU, hzy⟩ := (mem_closure_iff.mp hmem) ((U.1 : Set ↥X)) hopen hxU
    rw [Set.mem_singleton_iff] at hzy
    have hy2 : y ∈ ((U.1 : Set ↥X)) := by rw [← hzy]; exact hzU
    exact hy2
  have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
    (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
  have e1 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨x, hxU⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have e2 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨y, hyU⟩) = y :=
    hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hspec : hU.primeIdealOf ⟨y, hyU⟩ ⤳ hU.primeIdealOf ⟨x, hxU⟩ := by
    apply hind.specializes_iff.mp
    rw [e1, e2]
    exact h
  have hqp : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    have h2 := specializes_iff_mem_closure.mp hspec
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
    exact fun z hz => h2 hz
  have hne' : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≠ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro heq
    apply hne
    have hpe : hU.primeIdealOf ⟨y, hyU⟩ = hU.primeIdealOf ⟨x, hxU⟩ := PrimeSpectrum.ext heq
    exact e2.symm.trans (by rw [hpe]; exact e1)
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hne')
  let _ : Algebra Γ(X, U.1) ↑(X.presheaf.stalk x) := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have hmax : Ideal.map (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      = IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hmapmem : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hap
  have h0 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a = 0 := by
    rw [hbot] at hmapmem
    simpa using hmapmem
  have h1 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      = (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) 0 := by
    rw [h0, map_zero]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ↑(X.presheaf.stalk x)).mp h1
  have hca : (c : Γ(X, U.1)) * a = 0 := by
    rw [mul_zero] at hc
    exact hc
  have hcp : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := c.2
  have hcq : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := fun hc0 => hcp (hqp hc0)
  have hmem0 : (c : Γ(X, U.1)) * a ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [hca]
    exact Submodule.zero_mem _
  rcases (hU.primeIdealOf ⟨y, hyU⟩).isPrime.mem_or_mem hmem0 with hcc | haa
  · exact hcq hcc
  · exact haq haa
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
