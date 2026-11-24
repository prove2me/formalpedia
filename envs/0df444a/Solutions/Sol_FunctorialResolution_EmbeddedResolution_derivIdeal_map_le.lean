-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:46.445798+00:00
-- url     : https://prove2.me/submissions/b7ce1c7e-a71a-4e0c-9f63-dd5c14b5db20

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Theorems.Thm_Derivation_exists_derivation_mul_eq_of_isLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v w
namespace FunctorialResolution.EmbeddedResolution
variable {k : Type u} {S : Type v} {S' : Type w}
private theorem derivation_algebraMap_mem_map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S]
    [Algebra S S'] [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
    (D : Derivation k S' S') {a : S} (ha : a ∈ J) :
    D (algebraMap S S' a) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) := by
  obtain ⟨m, D₀, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
  refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_
  rw [hm a]
  exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v w
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} {S : Type v} {S' : Type w}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D x hx
  rw [IsLocalization.mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  have h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S)) := by rw [hax]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) :=
    derivation_algebraMap_mem_map_derivIdeal M J D a.2
  have hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := Ideal.mul_mem_left _ _ hA
  have hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))
  have h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
    have h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) =
        algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) -
          algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) := by
      linear_combination (algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax
    rw [h2]
    exact sub_mem hmem1 hmem2
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp
    ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)
end FunctorialResolution.EmbeddedResolution
