-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_opens_stalkIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:52.713331+00:00
-- url     : https://prove2.me/submissions/86735b49-4889-4eec-bc55-a34bfabc0731

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_mem_mul_mem_of_map_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) (hM : IsLocalization M S) (A B : Ideal R)
    (hA : Submodule.FG A)
    (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B) :
    ∃ u : R, u ∈ M ∧ ∀ a ∈ A, u * a ∈ B := by
  classical
  have := hM
  obtain ⟨G, hG⟩ := hA
  have key : ∀ a : R, ∃ u : R, u ∈ M ∧ (a ∈ A → u * a ∈ B) := by
    intro a
    by_cases ha : a ∈ A
    · have h1 : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
        hAB (Ideal.mem_map_of_mem _ ha)
      rw [IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)] at h1
      obtain ⟨⟨b, s⟩, hEq⟩ := h1
      rw [← map_mul] at hEq
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp hEq
      refine ⟨(c : R) * (s : R), M.mul_mem c.2 s.2, fun _ => ?_⟩
      have hcalc : (c : R) * (s : R) * a = (c : R) * (b : R) := by linear_combination hc
      rw [hcalc]
      exact Ideal.mul_mem_left B _ b.2
    · exact ⟨1, M.one_mem, fun hmem => absurd hmem ha⟩
  choose u huM huB using key
  refine ⟨∏ g ∈ G, u g, (Submonoid.prod_mem M fun g _ => huM g), ?_⟩
  intro a ha
  rw [← hG] at ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
      have hzG : z ∈ G := Finset.mem_coe.mp hz
      have hzA : z ∈ A := by rw [← hG]; exact Submodule.subset_span hz
      rw [← Finset.mul_prod_erase G u hzG]
      have hre : u z * (∏ g ∈ G.erase z, u g) * z
          = (∏ g ∈ G.erase z, u g) * (u z * z) := by ring
      rw [hre]
      exact Ideal.mul_mem_left B _ (huB z hzA)
  | zero => rw [mul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [mul_add]; exact B.add_mem hy hz
  | smul c y _ hy =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left B c hy
private theorem map_le_map_of_isUnit_mul_mem {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (w : R) (hw : IsUnit (φ w)) (A B : Ideal R)
    (hAB : ∀ a ∈ A, w * a ∈ B) :
    Ideal.map φ A ≤ Ideal.map φ B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  obtain ⟨t, ht⟩ := hw.exists_right_inv
  have h1 : φ (w * a) ∈ Ideal.map φ B := Ideal.mem_map_of_mem φ (hAB a ha)
  have h4 : t * φ (w * a) ∈ Ideal.map φ B := Ideal.mul_mem_left _ _ h1
  rw [map_mul, ← mul_assoc, mul_comm t (φ w), ht, one_mul] at h4
  exact Ideal.mem_comap.mpr h4
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (x : X) (h : stalkIdeal I x = stalkIdeal J x) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ y : X, y ∈ W → stalkIdeal I y = stalkIdeal J y := by
  obtain ⟨U, hxU, hU⟩ := Scheme.exists_isAffineOpen_mem x
  have hUaff : IsAffineOpen U := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let instAlg : Algebra Γ(X, U) ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have halg : (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) = (X.presheaf.germ U x hxU).hom := rfl
  have hloc : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have hmapeq : Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (I.ideal ⟨U, hU⟩)
      = Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (J.ideal ⟨U, hU⟩) := by
    have h1 := stalkIdeal_eq_map_germ I x ⟨U, hU⟩ hxU
    have h2 := stalkIdeal_eq_map_germ J x ⟨U, hU⟩ hxU
    rw [h1, h2] at h
    rw [halg]
    exact h
  obtain ⟨u₁, hu₁M, hu₁⟩ := exists_mem_mul_mem_of_map_le _ hloc (I.ideal ⟨U, hU⟩)
    (J.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq)
  obtain ⟨u₂, hu₂M, hu₂⟩ := exists_mem_mul_mem_of_map_le _ hloc (J.ideal ⟨U, hU⟩)
    (I.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq.symm)
  have hmb : ∀ (z : ↥X) (hz : z ∈ U),
      z ∈ X.basicOpen (u₁ * u₂) ↔ IsUnit ((X.presheaf.germ U z hz).hom (u₁ * u₂)) := by
    intro z hz
    exact X.mem_basicOpen (u₁ * u₂) z hz
  have hxunit : IsUnit ((X.presheaf.germ U x hxU).hom (u₁ * u₂)) := by
    have hmem : u₁ * u₂ ∈ (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl :=
      Submonoid.mul_mem _ hu₁M hu₂M
    have hone := IsLocalization.map_units
      (M := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
      (S := ↑(X.presheaf.stalk x)) ⟨u₁ * u₂, hmem⟩
    rw [halg] at hone
    exact hone
  refine ⟨X.basicOpen (u₁ * u₂), (hmb x hxU).mpr hxunit, ?_⟩
  intro y hy
  have hyU : y ∈ U := X.basicOpen_le (u₁ * u₂) hy
  have hyunit : IsUnit ((X.presheaf.germ U y hyU).hom (u₁ * u₂)) := (hmb y hyU).mp hy
  have hv1 : ∀ a ∈ I.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ J.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₂ * (u₁ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₁ a ha)
  have hv2 : ∀ a ∈ J.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ I.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₁ * (u₂ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₂ a ha)
  rw [stalkIdeal_eq_map_germ I y ⟨U, hU⟩ hyU, stalkIdeal_eq_map_germ J y ⟨U, hU⟩ hyU]
  exact le_antisymm
    (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv1)
    (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv2)
end FunctorialResolution.EmbeddedResolution
