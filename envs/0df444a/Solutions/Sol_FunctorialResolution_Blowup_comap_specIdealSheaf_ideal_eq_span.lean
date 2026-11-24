-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_specIdealSheaf_ideal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:49:21.908429+00:00
-- url     : https://prove2.me/submissions/930ad2b8-5605-47cf-aa02-f6336fd5765d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_Blowup_chartSectionsRingHom_chartRingHom
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
namespace FunctorialResolution.Blowup
theorem _root_.solution {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I) (a : ↥I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
      Ideal.span
        {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
  have hfac : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)
      = RingHom.comp (chartSectionsRingHom I h a (V : W.Opens) hV) (chartRingHom I a) := by
    ext r
    exact (chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV r).symm
  have h2 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)) I
      = Ideal.span
          {chartSectionsRingHom I h a (V : W.Opens) hV (chartRingHom I a (a : R))} := by
    rw [hfac, ← Ideal.map_map, map_chartRingHom_eq_span_singleton I a, Ideal.map_span, Set.image_singleton]
  rw [comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) V, h2,
    chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV (a : R)]
end FunctorialResolution.Blowup
