-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:47.652298+00:00
-- url     : https://prove2.me/submissions/41485825-183b-4af9-aca3-85b24351e4c4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_hom_ext_of_comp_eq

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
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I) :
    ∃ e : X₁ ≅ X₂, e.hom ≫ π₂ = π₁ := by
  obtain ⟨a, ha, -⟩ := h₂.2 X₁ π₁ h₁.1
  obtain ⟨b, hb, -⟩ := h₁.2 X₂ π₂ h₂.1
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · exact h₁.hom_ext_of_comp_eq h₁.1 (by rw [Category.assoc, hb, ha]) (Category.id_comp π₁)
  · exact h₂.hom_ext_of_comp_eq h₂.1 (by rw [Category.assoc, ha, hb]) (Category.id_comp π₂)
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
