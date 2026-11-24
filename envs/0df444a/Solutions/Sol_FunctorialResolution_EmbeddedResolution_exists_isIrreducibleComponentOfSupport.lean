-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_isIrreducibleComponentOfSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:50.943301+00:00
-- url     : https://prove2.me/submissions/6996d810-317a-4138-b957-1d5968278f0c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (D : X.IdealSheafData) (x : X)
    (hx : x ∈ (D.support : Set X)) :
    ∃ C : Set X, IsIrreducibleComponentOfSupport D C ∧ x ∈ C := by
  have hchain : ∀ c ⊆ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hch hne
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨t, ht⟩ := hne
      obtain ⟨y, hy⟩ := (hcS ht).1.nonempty
      exact ⟨y, t, ht, hy⟩
    · rintro u v hu hv ⟨y, ⟨q, hq, hyq⟩, hyu⟩ ⟨z, ⟨r, hr, hzr⟩, hzv⟩
      rcases hch.total hq hr with h | h
      · obtain ⟨w, hw, hwuv⟩ := (hcS hr).1.2 u v hu hv ⟨y, h hyq, hyu⟩ ⟨z, hzr, hzv⟩
        exact ⟨w, ⟨r, hr, hw⟩, hwuv⟩
      · obtain ⟨w, hw, hwuv⟩ := (hcS hq).1.2 u v hu hv ⟨y, hyq, hyu⟩ ⟨z, h hzr, hzv⟩
        exact ⟨w, ⟨q, hq, hw⟩, hwuv⟩
    · exact Set.sUnion_subset fun t ht => (hcS ht).2
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty
    {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)} hchain {x}
    ⟨isIrreducible_singleton, Set.singleton_subset_iff.mpr hx⟩
  exact ⟨m, ⟨hm.1.1, fun C' hC' hmC' hC'S =>
    Set.Subset.antisymm (hm.2 ⟨hC', hC'S⟩ hmC') hmC', hm.1.2⟩, hxm rfl⟩
end FunctorialResolution.EmbeddedResolution
