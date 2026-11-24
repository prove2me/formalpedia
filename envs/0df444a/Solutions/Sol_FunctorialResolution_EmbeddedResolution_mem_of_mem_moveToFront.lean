-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_of_mem_moveToFront
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:09.839637+00:00
-- url     : https://prove2.me/submissions/a2980f05-4b9b-4afe-958e-42dea97c9b05

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (E : List α) (j : ℕ) (hj : j < E.length) (D : α)
    (hD : D ∈ moveToFront E j) : D ∈ E := by
  rw [moveToFront_eq_cons E j hj] at hD
  rcases List.mem_cons.mp hD with h1 | h2
  · subst h1
    simp
  · exact List.mem_of_mem_eraseIdx h2
end FunctorialResolution.EmbeddedResolution
