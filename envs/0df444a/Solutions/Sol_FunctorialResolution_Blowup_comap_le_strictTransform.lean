-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_le_strictTransform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:18.369979+00:00
-- url     : https://prove2.me/submissions/d5ed9a12-6325-4190-a526-8bb4fba0416f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformImmersion_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransform_eq_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section
namespace FunctorialResolution.Blowup
theorem _root_.solution {X X₁ : Scheme.{u}} (p : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    D.comap p ≤ strictTransform p Z D := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq]
  have h := Scheme.Hom.le_ker_comp (strictTransformOpens p Z D).ι (D.comap p).subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h
end FunctorialResolution.Blowup
