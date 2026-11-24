-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_specIdealSheaf_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:12.461901+00:00
-- url     : https://prove2.me/submissions/b4d1a61f-94a6-4c09-b03c-384374196e1f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_FunctorialResolution_Blowup_specIdealSheaf_ideal_top


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
namespace FunctorialResolution.Blowup
theorem _root_.solution {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    ((specIdealSheaf I).comap g).ideal V = Ideal.map (sectionsRingHom g (V : W.Opens)) I := by
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) g
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ V
      (le_top.trans (Scheme.Hom.preimage_top g).ge)
  rw [specIdealSheaf_ideal_top, Ideal.map_map] at h1
  exact h1
end FunctorialResolution.Blowup
