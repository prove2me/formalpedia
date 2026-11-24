-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:23.679803+00:00
-- url     : https://prove2.me/submissions/cc275551-67c1-496d-b028-eb610dc23a2f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_of_isOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (U : X.Opens) :
    IsBlowupAlongIdealSheaf (π ∣_ U) (I.comap U.ι) := by
  have key : ∀ {W : Scheme.{u}} (g : W ⟶ U.toScheme),
      (I.comap U.ι).comap g = I.comap (g ≫ U.ι) := by
    intro W g
    rw [Scheme.IdealSheafData.comap_comp]
  constructor
  · rw [key (π ∣_ U), morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    exact h.1.comap_of_isOpenImmersion (π ⁻¹ᵁ U).ι
  · intro W g hg
    rw [key g] at hg
    obtain ⟨k, hk, hk'⟩ := h.2 W (g ≫ U.ι) hg
    have hrange : Set.range ⇑k.base ⊆ Set.range ⇑(π ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show π.base (k.base w) ∈ U
      have h1 : (k ≫ π).base w = (g ≫ U.ι).base w := by rw [hk]
      have h2 : π.base (k.base w) = U.ι.base (g.base w) := h1
      rw [h2]
      exact (g.base w).2
    refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange, ?_, ?_⟩
    · show IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange ≫ π ∣_ U = g
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac]
      exact hk
    · intro y hy
      have hy' : y ≫ π ∣_ U = g := hy
      rw [← cancel_mono (π ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
      refine hk' _ ?_
      show (y ≫ (π ⁻¹ᵁ U).ι) ≫ π = g ≫ U.ι
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy']
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
