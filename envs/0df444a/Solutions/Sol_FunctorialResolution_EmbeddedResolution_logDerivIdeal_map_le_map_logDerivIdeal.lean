-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdeal_map_le_map_logDerivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:18.193709+00:00
-- url     : https://prove2.me/submissions/6d089803-d382-49b3-8b4e-3b442ff142e2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_mem_tangentDerivations_mul_eq
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap


section
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
private theorem exists_mem_mul_algebraMap_eq_of_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx
  exact ⟨u.1, u.2, u.1.2, hu⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩
  intro D hD x hx
  obtain ⟨m, D₁, hD₁, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨y, t, hy, hxt⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M J hx
  have hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S') :=
    Ideal.map_mono (le_logDerivIdeal k P J) hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp only [smul_eq_mul] at h1
  have e1 := hm y
  have e2 := hm (t : S)
  have hmul : algebraMap S S' ((m : S) * (t : S)) * D x
      = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + e1 - x * e2
  have hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    refine sub_mem ?_ ?_
    · exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)
    · exact Ideal.mul_mem_right _ _ hxL
  have hu : IsUnit (algebraMap S S' ((m : S) * (t : S))) := by
    rw [map_mul]
    exact (IsLocalization.map_units (M := M) (S := S') m).mul
      (IsLocalization.map_units (M := M) (S := S') t)
  obtain ⟨u, hu'⟩ := hu
  have hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' ((m : S) * (t : S)) * D x) := by
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  rw [hrw]
  exact Ideal.mul_mem_left _ _ hmem
end FunctorialResolution.EmbeddedResolution
