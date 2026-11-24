-- Prove2me | solution 1 for FunctorialResolution.Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:26.38838+00:00
-- url     : https://prove2.me/submissions/904d5dda-52c8-45de-9123-cb27b0c27471

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
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
theorem _root_.solution {X X' : Scheme.{u}} (f : X' ⟶ X) :
    IsLocallyGeneratedByNonZeroDivisor ((⊤ : X.IdealSheafData).comap f) := by
  intro x
  obtain ⟨U, hU, -⟩ := exists_affineOpen_le X (f.base x) ⊤ trivial
  obtain ⟨V, hV, hVU⟩ := exists_affineOpen_le X' x (f ⁻¹ᵁ (U : X.Opens)) hU
  refine ⟨V, 1, hV, one_mem _, ?_⟩
  have h1 : ((⊤ : X.IdealSheafData).ideal U) = ⊤ := by simp
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (⊤ : X.IdealSheafData) f U V hVU, h1,
    Ideal.map_top, Ideal.span_singleton_one]
end FunctorialResolution.Blowup
