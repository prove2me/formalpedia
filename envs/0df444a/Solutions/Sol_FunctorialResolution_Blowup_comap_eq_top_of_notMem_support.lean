-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:01.455537+00:00
-- url     : https://prove2.me/submissions/c79f1c18-bf89-4c4f-884b-1949629a95af

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) (h : ∀ x : X', f.base x ∉ I.support) :
    I.comap f = ⊤ := by
  have hs : (I.comap f).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact absurd (show f.base x ∈ I.support from hx) (h x)
    · exact (show False from hx).elim
  exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hs
end FunctorialResolution.Blowup
