-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_map_eq_self_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:40.570803+00:00
-- url     : https://prove2.me/submissions/5d7e9ac7-82cc-450f-952d-b2891b352df9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatDescent
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_map_eq_map_comap_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [AlgebraicGeometry.Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s : W ⟶ Q, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap I q)
  have h1 := Scheme.IdealSheafData.comap_map_le (I.comap q) q
  have h2 : (((I.comap q).map q).comap q).comap s ≤ ((I.comap q).comap s) :=
    Scheme.IdealSheafData.comap_mono s h1
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h2
end FunctorialResolution.EmbeddedResolution
