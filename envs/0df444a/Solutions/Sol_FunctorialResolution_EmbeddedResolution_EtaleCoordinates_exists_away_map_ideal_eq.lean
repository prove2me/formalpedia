-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_map_ideal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:36.844858+00:00
-- url     : https://prove2.me/submissions/bf38918e-b865-4c2f-8c6a-d84a0d1479fb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealGeneratorsFromBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
private theorem algebraMap_mem_map_of_mul_mem {S : Type*} [CommRing S] (G : S) (T : Type*)
    [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers G) T] (J : Ideal S) (g r x : S)
    (hG : G = g * r) (hgx : g * x ∈ J) :
    algebraMap S T x ∈ Ideal.map (algebraMap S T) J := by
  have hGu : IsUnit (algebraMap S T G) :=
    IsLocalization.map_units T (⟨G, Submonoid.mem_powers G⟩ : Submonoid.powers G)
  rw [hG, map_mul] at hGu
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hGu
  have hx : algebraMap S T x = (↑u⁻¹ : T) * algebraMap S T (g * x) := by
    rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgx)
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S (Localization.Away g)) I =
        Ideal.map (algebraMap S (Localization.Away g)) J := by
  classical
  obtain ⟨tI, htI⟩ := hI
  obtain ⟨tJ, htJ⟩ := hJ
  have keyI : ∀ u : S, ∃ g : S, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J) := by
    intro u
    by_cases hu : u ∈ I
    · have hmem : algebraMap S A u ∈ Ideal.map (algebraMap S A) J := by
        rw [← h]
        exact Ideal.mem_map_of_mem _ hu
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgu⟩ := hmem
      exact ⟨g, hg, fun _ => hgu⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩
  have keyJ : ∀ v : S, ∃ g : S, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I) := by
    intro v
    by_cases hv : v ∈ J
    · have hmem : algebraMap S A v ∈ Ideal.map (algebraMap S A) I := by
        rw [h]
        exact Ideal.mem_map_of_mem _ hv
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgv⟩ := hmem
      exact ⟨g, hg, fun _ => hgv⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩
  choose gI hgI hgIu using keyI
  choose gJ hgJ hgJu using keyJ
  let G : S := (∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v
  have hGmem : G ∈ q.primeCompl :=
    Submonoid.mul_mem _ (Submonoid.prod_mem _ fun u _ => hgI u)
      (Submonoid.prod_mem _ fun v _ => hgJ v)
  refine ⟨G, hGmem, le_antisymm ?_ ?_⟩
  · rw [← htI, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ tI := Finset.mem_coe.mp hu
    have huI : u ∈ I := by
      rw [← htI]
      exact Ideal.subset_span hu
    have hGeq : G = gI u * ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) := by
      show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _
      rw [← Finset.mul_prod_erase tI gI hu']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) J (gI u)
      ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u hGeq (hgIu u huI)
  · rw [← htJ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ tJ := Finset.mem_coe.mp hv
    have hvJ : v ∈ J := by
      rw [← htJ]
      exact Ideal.subset_span hv
    have hGeq : G = gJ v * ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) := by
      show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _
      rw [← Finset.mul_prod_erase tJ gJ hv']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) I (gJ v)
      ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v hGeq (hgJu v hvJ)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
