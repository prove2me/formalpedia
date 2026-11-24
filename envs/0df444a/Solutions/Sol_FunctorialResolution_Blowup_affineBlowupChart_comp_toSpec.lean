-- Prove2me | solution 1 for FunctorialResolution.Blowup.affineBlowupChart_comp_toSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:17.937177+00:00
-- url     : https://prove2.me/submissions/b483f5ca-e2ba-4ad0-93c0-c4d4c141c0c1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a ≫ AffineBlowup.toSpec I =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a))) := by
  show AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos ≫
      (AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))) =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a)))
  rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← AlgebraicGeometry.Spec.map_comp]
  rfl
end FunctorialResolution.Blowup
