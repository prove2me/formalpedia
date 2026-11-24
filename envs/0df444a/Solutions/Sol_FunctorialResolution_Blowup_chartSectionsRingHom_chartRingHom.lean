-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartSectionsRingHom_chartRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:27.548886+00:00
-- url     : https://prove2.me/submissions/08542470-d9d7-479e-b8f6-ef3e594d2433

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_comp_chartSectionsIso_hom


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
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) (r : R) :
    chartSectionsRingHom I h b V hV (chartRingHom I b r) =
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  have key : CommRingCat.ofHom (chartRingHom I b) ≫ ((chartSectionsIso I b).hom ≫
        h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV)
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (h ≫ AffineBlowup.toSpec I).appLE ⊤ V
          (le_top.trans (Scheme.Hom.preimage_top (h ≫ AffineBlowup.toSpec I)).ge) := by
    rw [← Category.assoc, chartRingHom_comp_chartSectionsIso_hom, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : CommRingCat.of R ⟶ Γ(W, V) => φ.hom r) key
end FunctorialResolution.Blowup
