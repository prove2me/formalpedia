-- Prove2me | solution 1 for FunctorialResolution.Blowup.isLocallyGeneratedByNonZeroDivisor_comap_toSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:51:42.455268+00:00
-- url     : https://prove2.me/submissions/8363633d-0eb0-4442-ad1d-693b60dc3434

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Theorems.Thm_FunctorialResolution_Blowup_ideal_comap_toSpec_chart_eq_span
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_mem_nonZeroDivisors
import Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) :
    IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (AffineBlowup.toSpec I)) := by
  intro x
  obtain ⟨a, hx⟩ : ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base :=
    ⟨(affineBlowupAffineOpenCover I).idx x, (affineBlowupAffineOpenCover I).covers x⟩
  have hW := (isAffineOpen_top (Spec (CommRingCat.of
      (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))))).image_of_isOpenImmersion
      (affineBlowupChart I a)
  refine ⟨⟨_, hW⟩, (chartSectionsIso I a).hom.hom (chartRingHom I a (a : R)), ?_, ?_,
    ideal_comap_toSpec_chart_eq_span I a hW⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, trivial, hy⟩
  · exact map_mem_nonZeroDivisors_of_iso (chartSectionsIso I a) (chartRingHom_mem_nonZeroDivisors I a)
end FunctorialResolution.Blowup
