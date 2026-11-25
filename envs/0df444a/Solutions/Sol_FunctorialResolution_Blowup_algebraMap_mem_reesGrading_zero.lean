-- Prove2me | solution 1 for FunctorialResolution.Blowup.algebraMap_mem_reesGrading_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:52.185041+00:00
-- url     : https://prove2.me/submissions/56e26959-f56b-44b5-baa5-fa6527fbd308

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open FunctorialResolution FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r ∈ reesGrading I 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (reesGrading_one_mem I)
end FunctorialResolution.Blowup
