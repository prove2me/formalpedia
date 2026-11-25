-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_isBlowupAlongIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:14.381776+00:00
-- url     : https://prove2.me/submissions/8331c8f6-358a-433f-8c57-0b1930c78f8c

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
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I)
    {a b : X₁ ⟶ X₂} (ha : a ≫ π₂ = π₁) (hb : b ≫ π₂ = π₁) : a = b :=
  h₂.hom_ext_of_comp_eq h₁.1 ha hb
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
