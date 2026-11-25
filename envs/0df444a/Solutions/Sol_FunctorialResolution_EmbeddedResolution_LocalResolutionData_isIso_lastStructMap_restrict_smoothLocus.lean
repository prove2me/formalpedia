-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.isIso_lastStructMap_restrict_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:25.856308+00:00
-- url     : https://prove2.me/submissions/53ec5583-6d1d-452b-9fff-c02ce80d0312

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SmoothLocusIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_isPullback_chartToLastObj
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_preimage_smoothLocus_cover_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
private theorem isIso_pullback_snd_restrict_smoothLocus (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsIso (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
  have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
  have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
  have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
  have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
  have hw : (((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) ≫
        (d.cover.f i ∣_ f.smoothLocus)) ≫ f.smoothLocus.ι
      = ((((d.seq i).lastStructMap ⁻¹ᵁ (d.cover.f i ⁻¹ᵁ f.smoothLocus)).ι) ≫ d.chartToLastObj i)
        ≫ s.lastStructMap := by
    rw [Category.assoc, hc.w]
    exact hbig.w
  have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
      (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (s.lastStructMap ∣_ f.smoothLocus) := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [hp.lift_snd, hc.w]
      exact hbig
    · rw [hp.lift_fst]
  have hiso : IsIso ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact (d.isResolution i).2.2.1
  have hcomp : IsIso (hsq.flip.isoPullback.hom ≫
      pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
    rw [hsq.flip.isoPullback_hom_snd]
    exact hiso
  exact IsIso.of_isIso_comp_left hsq.flip.isoPullback.hom
    (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))
end LocalResolutionData
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Scheme.{u}
      (Scheme.Cover.pullbackHom (smoothLocusOpenCover d) (s.lastStructMap ∣_ f.smoothLocus) i) := by
    intro i
    exact isIso_pullback_snd_restrict_smoothLocus d i
  have key : MorphismProperty.isomorphisms Scheme.{u} (s.lastStructMap ∣_ f.smoothLocus) :=
    IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover d) hh
  exact key
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
