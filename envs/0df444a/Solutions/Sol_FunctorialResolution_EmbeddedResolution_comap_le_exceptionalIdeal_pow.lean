-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_le_exceptionalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:37.764186+00:00
-- url     : https://prove2.me/submissions/c24b2b5c-2a39-4375-99b2-091cfb347974

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_pow
import Theorems.Thm_FunctorialResolution_Blowup_exceptionalIdeal_eq_comap


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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
variable {X X₁ : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (π : X₁ ⟶ X) {Z I : X.IdealSheafData} {n : ℕ}
    (hI : I ≤ Z ^ n) : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := by
  rw [Blowup.exceptionalIdeal_eq_comap, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
  apply AlgebraicGeometry.Scheme.IdealSheafData.comap_mono
  exact hI
end FunctorialResolution.EmbeddedResolution
