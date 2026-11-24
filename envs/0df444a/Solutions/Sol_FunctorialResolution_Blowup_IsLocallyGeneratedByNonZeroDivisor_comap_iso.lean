-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:12.734708+00:00
-- url     : https://prove2.me/submissions/bf37329b-5d2b-4723-8ad6-2801e558eac8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {X' X'' : Scheme.{u}} {J : X'.IdealSheafData}
    (hJ : IsLocallyGeneratedByNonZeroDivisor J) (e : X'' ≅ X') :
    IsLocallyGeneratedByNonZeroDivisor (J.comap e.hom) := by
  intro x
  obtain ⟨U, f, hxU, hf, hJU⟩ := hJ (e.hom.base x)
  refine ⟨⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩,
    (e.hom.appLE (U : X'.Opens) (e.hom ⁻¹ᵁ (U : X'.Opens)) le_rfl).hom f, hxU, ?_, ?_⟩
  · exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (sectionsIsoPreimage e (U : X'.Opens)) hf
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J e.hom U
      ⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩ le_rfl, hJU,
      Ideal.map_span, Set.image_singleton]
end IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.Blowup
