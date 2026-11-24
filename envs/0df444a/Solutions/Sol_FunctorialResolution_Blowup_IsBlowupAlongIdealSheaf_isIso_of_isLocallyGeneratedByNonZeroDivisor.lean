-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.isIso_of_isLocallyGeneratedByNonZeroDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:35.870351+00:00
-- url     : https://prove2.me/submissions/3396d02e-dd9f-489a-89f6-076a579dc18c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_hom_ext_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace FunctorialResolution.Blowup
private theorem isLocallyGeneratedByNonZeroDivisor_comap_id {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsLocallyGeneratedByNonZeroDivisor (I.comap (𝟙 X)) := by
  intro x
  obtain ⟨U, f, hxU, hf, hIspan⟩ := hI x
  refine ⟨U, f, hxU, hf, ?_⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) U U le_rfl,
    appLE_eq_id_of_eq_id (𝟙 X) rfl (U : X.Opens) le_rfl, hIspan]
  simp
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsIso π := by
  obtain ⟨s, hs, -⟩ := h.2 X (𝟙 X) (isLocallyGeneratedByNonZeroDivisor_comap_id hI)
  refine ⟨⟨s, ?_, hs⟩⟩
  exact h.hom_ext_of_comp_eq h.1 (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp π)
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
