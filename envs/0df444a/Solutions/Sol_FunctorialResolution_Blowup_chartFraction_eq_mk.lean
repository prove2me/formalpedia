-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartFraction_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:50.353115+00:00
-- url     : https://prove2.me/submissions/e5f02881-7c41-4caf-8298-832361d280d9

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
theorem _root_.solution (I : Ideal R) (a b : ↥I) :
    chartFraction I a b =
      HomogeneousLocalization.mk
        { deg := 1
          num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
          den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
          den_mem := reesGenerator_pow_one_mem_powers I a } := rfl
end FunctorialResolution.Blowup
