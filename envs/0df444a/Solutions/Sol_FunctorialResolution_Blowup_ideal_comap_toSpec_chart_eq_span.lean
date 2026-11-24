-- Prove2me | solution 1 for FunctorialResolution.Blowup.ideal_comap_toSpec_chart_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:21.446034+00:00
-- url     : https://prove2.me/submissions/ccde6dad-9c4c-46e7-9558-5ed7f6f0e7b5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Theorems.Thm_FunctorialResolution_Blowup_specIdealSheaf_ideal_top
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_comp_chartSectionsIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_FunctorialResolution_Blowup_map_chartRingHom_eq_span_singleton


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
theorem _root_.solution (I : Ideal R) (a : ↥I)
    (hW : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (AffineBlowup.toSpec I)).ideal ⟨_, hW⟩ =
      Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
  have hcomp := congrArg CommRingCat.Hom.hom (chartRingHom_comp_chartSectionsIso_hom I a)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hcomp
  have key : Ideal.map ((AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
        (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)).hom
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)
      = Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map, map_chartRingHom_eq_span_singleton, Ideal.map_span,
      Set.image_singleton]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) (AffineBlowup.toSpec I)
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ ⟨_, hW⟩
      (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)]
  rw [specIdealSheaf_ideal_top]
  exact key
end FunctorialResolution.Blowup
