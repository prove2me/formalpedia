-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:10.409385+00:00
-- url     : https://prove2.me/submissions/780ae961-6b76-485c-9513-9e8a59e33279

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_coord

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (v : Type u) (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have h2 : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      ((affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.C c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp
    rw [← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
    simp
  rw [← key, appTop_hom_inv_apply]
end FunctorialResolution.EmbeddedResolution
