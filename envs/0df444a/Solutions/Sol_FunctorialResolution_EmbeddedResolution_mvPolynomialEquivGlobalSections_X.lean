-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:27.707154+00:00
-- url     : https://prove2.me/submissions/dbdad138-eeb3-4344-885e-030dba1c6fd4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem affineSpaceIsoSpecMvPolynomial_inv_appTop_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.X i) := by
  rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [mvPolynomialEquivGlobalSections_apply, ← affineSpaceIsoSpecMvPolynomial_inv_appTop_coord k v i, appTop_hom_inv_apply]
end FunctorialResolution.EmbeddedResolution
