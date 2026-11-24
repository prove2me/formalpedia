-- Prove2me | solution 1 for FunctorialResolution.Blowup.isLocallyGeneratedByNonZeroDivisor_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:26.931117+00:00
-- url     : https://prove2.me/submissions/4d38ab15-10d4-428b-952a-d691b5125d77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
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
private theorem exists_affineOpen_le (X : Scheme.{u}) (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution (X : Scheme.{u}) :
    IsLocallyGeneratedByNonZeroDivisor (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_le X x ⊤ trivial
  refine ⟨U, 1, hxU, one_mem _, ?_⟩
  simp
end FunctorialResolution.Blowup
